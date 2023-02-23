use std::collections::HashMap;
use std::alloc::{GlobalAlloc, System, Layout};
use std::fmt::Write;
use std::ptr::NonNull;
use anyhow::{Result, anyhow};
use std::mem::size_of;

#[repr(C)]
#[derive(Clone,Copy)]
enum ObjType {
    Cons,
    Closure,
}

#[repr(C)]
#[derive(Clone,Copy)]
enum ValueType {
    Nil,
    I32,
    True,
    False,
    Undef,
    Symbol,
    Native,
}

type Value = u64;
pub type NativeId = u32;
pub type SymbolId = u32;
pub type FuncId = u32;
#[repr(C)]
struct ObjHead {
    value: u32,
    obj_type: ObjType,
}

#[repr(C)]
struct ObjCons {
    head: ObjHead,
    car: Value,
    cdr: Value,
}

#[repr(C)]
struct ObjClosure {
    head: ObjHead,
    func_id: FuncId,
    env: Value,
}

#[repr(C)]
#[derive(Debug, Clone)]
pub struct OpaqueValue(Value);

impl OpaqueValue {
    fn from_objhead_ptr(ptr:*mut ObjHead) -> Self{
        OpaqueValue(unsafe {std::mem::transmute(ptr)} )
    }
    fn from_value(value: u32, value_type: ValueType) -> Self {
        OpaqueValue(((value as u64) << 32) + ((value_type as u64) << 1) + 1)
    }
    pub fn get_obj(&self) -> Obj {
        if self.0 %2 == 1 {
            // value
            let value = (self.0 >> 32) as u32;
            let value_type = ((self.0 & 0xffff) >> 1) as u64;
            if value_type == ValueType::I32 as u64 {
                Obj::I32(value as i32)
            } else if value_type == ValueType::Nil as u64 {
                Obj::Nil
            } else if value_type == ValueType::Symbol as u64 {
                Obj::Symbol(value)
            } else if value_type == ValueType::Native as u64 {
                Obj::Native(value)
            } else if value_type == ValueType::True as u64 {
                Obj::True
            } else if value_type == ValueType::False as u64 {
                Obj::False
            } else if value_type == ValueType::Undef as u64 {
                Obj::Undef
            } else {
                panic!("unexpected value type {}", value_type)
            }
        } else {
            // pointer
            let ptr: *mut ObjHead = unsafe{ std::mem::transmute(self.0) };
            match unsafe { (*ptr).obj_type } {
                ObjType::Cons => Obj::Cons(OpaqueValueCons(self.0 as *mut ObjCons)),
                ObjType::Closure => Obj::Closure(OpaqueValueClosure(self.0 as *mut ObjClosure)),
            }
        }
    }
}


#[derive(Debug, Clone)]
pub struct OpaqueValueCons(*mut ObjCons);

impl OpaqueValueCons {
    pub fn set_car(&self, v: OpaqueValue) {
        unsafe {(*self.0).car = v.0;}
    }
    pub fn set_cdr(&self, v: OpaqueValue) {
        unsafe {(*self.0).cdr = v.0;}
    }
    pub fn get_car(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0).car})
    }
    pub fn get_cdr(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0).cdr})
    }
}

#[derive(Debug, Clone)]
pub struct OpaqueValueClosure(*mut ObjClosure);

impl OpaqueValueClosure {
    pub fn get_func_id(&self) -> FuncId {
        unsafe {(*self.0).func_id}
    }
    pub fn get_env(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0).env})
    }
}

#[derive(Debug, Clone)]
pub enum Obj {
    Nil,
    True,
    False,
    Undef,
    I32(i32),
    Native(NativeId),
    Symbol(SymbolId),
    Cons(OpaqueValueCons),
    Closure(OpaqueValueClosure),
}

pub struct ObjPool {
    layout: Layout,
    alloced: *mut u8,
    current: *mut u8,
    from_space: *mut u8,
    to_space: *mut u8,
    pool_size: usize,
    symbols: Vec<String>,
    symbols_map: HashMap<String, SymbolId>,
    head_entry: NonNull<PtrNode>,
    tail_entry: NonNull<PtrNode>,
}


impl Drop for ObjPool {
    fn drop(&mut self) {
        unsafe {System.dealloc(self.alloced, self.layout)}
    }
}

struct PtrNode {
    next: Option<NonNull<PtrNode>>,
    prev: Option<NonNull<PtrNode>>,
    element: Value,
}

impl PtrNode {
    fn new_ptr(value: OpaqueValue) -> NonNull<PtrNode> {
        Box::leak(
            Box::new(
                PtrNode {
                    prev: None,
                    next: None,
                    element: value.0,
                }
            )
        ).into()
    }
}

pub struct Ptr(NonNull<PtrNode>);

impl Ptr {
    pub fn get_value(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0.as_ptr()).element} )
    }
}

impl Drop for Ptr {
    fn drop(&mut self) {
        // TODO
    }
}

impl ObjPool {
    pub fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size * 2, 8).unwrap();
        let ptr = unsafe { System.alloc(layout)};
        let head_entry: NonNull<PtrNode> = PtrNode::new_ptr(OpaqueValue::from_value(0, ValueType::Nil));
        let tail_entry: NonNull<PtrNode> = PtrNode::new_ptr(OpaqueValue::from_value(0, ValueType::Nil));
        unsafe {
            (*head_entry.as_ptr()).next = Some(tail_entry);
            (*tail_entry.as_ptr()).prev = Some(head_entry);
        }
        Self {
            layout,
            alloced: ptr,
            current: ptr,
            from_space: ptr,
            to_space: unsafe { ptr.add(size)},
            pool_size: size,
            symbols: Vec::new(),
            symbols_map: HashMap::new(),
            head_entry,
            tail_entry,
        }
    }
    pub fn ptr(&mut self, value: OpaqueValue) -> Ptr {
        let new_entry = PtrNode::new_ptr(value);
        unsafe {
            let second_last_entry = (*self.tail_entry.as_ptr()).prev.unwrap();
            (*new_entry.as_ptr()).prev = Some(second_last_entry);
            (*new_entry.as_ptr()).next = Some(self.tail_entry);
            (*self.tail_entry.as_ptr()).prev = Some(new_entry);
            (*second_last_entry.as_ptr()).next = Some(new_entry);
        }
        Ptr(new_entry as NonNull<PtrNode>)
    }
    unsafe fn alloc(&mut self, size: usize, value: u32, obj_type: ObjType) -> Result<* mut ObjHead> {
        let size = (size + 1) / 2 * 2;
        if self.current.add(size) >= self.from_space.add(self.pool_size) {
            return Err(anyhow!("no space left in pool"));
        }
        let ptr = self.current as *mut ObjHead;
        self.current = unsafe {self.current.add(size)};
        unsafe {
            (*ptr).value = value;
            (*ptr).obj_type = obj_type;
        }
        Ok(ptr)
    }
    pub fn get_i32(&self, i: i32) -> OpaqueValue {
        OpaqueValue::from_value(i as u32, ValueType::I32)
    }
    pub fn get_native(&self, i: NativeId) -> OpaqueValue {
        OpaqueValue::from_value(i as u32, ValueType::Native)
    }
    pub fn get_nil(&self) -> OpaqueValue {
        OpaqueValue::from_value(0, ValueType::Nil)
    }
    pub fn get_true(&self) -> OpaqueValue {
        OpaqueValue::from_value(0, ValueType::True)
    }
    pub fn get_false(&self) -> OpaqueValue {
        OpaqueValue::from_value(0, ValueType::False)
    }
    pub fn get_undef(&self) -> OpaqueValue {
        OpaqueValue::from_value(0, ValueType::Undef)
    }
    pub fn get_symbol_str(&self, idx: SymbolId) -> String {
        self.symbols[idx as usize].to_owned()
    }
    pub fn get_symbol_from_idx(&self, idx: SymbolId) -> OpaqueValue {
        OpaqueValue::from_value(idx, ValueType::Symbol)
    }
    pub fn get_symbol_idx(&mut self, str: &str) -> SymbolId {
        if let Some(idx) = self.symbols_map.get(str) {
            *idx
        } else {
            let idx = self.symbols.len() as SymbolId;
            self.symbols.push(str.to_owned());
            self.symbols_map.insert(str.to_owned(), idx);
            idx
        }
    }
    pub fn get_symbol(&mut self, str: &str) -> Result<OpaqueValue> {
        let idx = self.get_symbol_idx(str);
        Ok(self.get_symbol_from_idx(idx))
    }
    pub fn alloc_cons(&mut self, car: OpaqueValue, cdr: OpaqueValue) -> Result<OpaqueValue> {
        let car = self.ptr(car);
        let cdr = self.ptr(cdr);
        let ptr = unsafe { self.alloc(size_of::<ObjCons>(), 0, ObjType::Cons)? };
        unsafe {
            let ptr = ptr as *mut ObjCons;
            (*ptr).car = car.get_value().0;
            (*ptr).cdr = cdr.get_value().0;
        }
        Ok(OpaqueValue::from_objhead_ptr(ptr))
    }
    pub fn alloc_closure(&mut self, func_id: FuncId, env: OpaqueValue) -> Result<OpaqueValue> {
        let env = self.ptr(env);
        let ptr = unsafe { self.alloc(size_of::<ObjClosure>(), 0, ObjType::Closure)? };
        unsafe {
            let ptr = ptr as *mut ObjClosure;
            (*ptr).func_id = func_id;
            (*ptr).env = env.get_value().0;
        }
        Ok(OpaqueValue::from_objhead_ptr(ptr))
    }
    pub fn write_to_string(&self, v: &OpaqueValue) -> String {
        let mut buf = String::new();
        self.write(&mut buf, v).unwrap();
        buf
    }
    pub fn write<W:Write>(&self, w: &mut W, v: &OpaqueValue) -> Result<()> {
        match v.get_obj() {
            Obj::Nil => {write!(w, "()")?;}
            Obj::True => {write!(w, "#t")?;}
            Obj::False => {write!(w, "#f")?;}
            Obj::Undef => {write!(w, "#undef")?;}
            Obj::I32(i) => {write!(w, "{}",i)?;}
            Obj::Native(i) => {write!(w, "#native:{}#", i)?;}
            Obj::Symbol(s) => {write!(w, "{}", self.get_symbol_str(s))?;}
            Obj::Cons(_) => {self.write_list(w, v)?;}
            Obj::Closure(_) => {write!(w, "#closure#")?;}
        }
        Ok(())
    }
    fn write_list<W:Write>(&self, w: &mut W, v: &OpaqueValue) -> Result<()> {
        write!(w, "(")?;
        let mut current: OpaqueValue = v.to_owned();
        let mut first = true;
        loop {
            match current.get_obj() {
                Obj::Cons(cons) => {
                    if !first {
                        write!(w, " ")?;
                    }
                    first = false;
                    self.write(w, &cons.get_car())?;
                    current = cons.get_cdr();
                },
                Obj::Nil => {break}
                _ => {
                    write!(w, ". ")?;
                    self.write(w, &current)?;
                    break
                }
            }
        }
        write!(w, ")")?;
        Ok(())
    }
}

pub fn equal(v1: &OpaqueValue, v2: &OpaqueValue) -> bool {
    match (v1.get_obj(), v2.get_obj()) {
        (Obj::True, Obj::True) => true,
        (Obj::False, Obj::False) => true,
        (Obj::Undef, Obj::Undef) => true,
        (Obj::I32(i1), Obj::I32(i2)) => i1 == i2,
        (Obj::Nil, Obj::Nil) => true,
        (Obj::Symbol(s1), Obj::Symbol(s2)) => s1 == s2,
        (Obj::Cons(c1), Obj::Cons(c2)) => equal(&c1.get_car(), &c2.get_car()) && equal(&c1.get_car(), &c2.get_car()),
        _ => false,
    }
}

struct ListIterator {
    current: OpaqueValue
}

impl Iterator for ListIterator {
    type Item = Result<OpaqueValue>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.current.get_obj() {
            Obj::Cons(cons) => {
                let car = cons.get_car();
                self.current = cons.get_cdr();
                Some(Ok(car))
            },
            Obj::Nil => None,
            _ => {
                self.current = OpaqueValue::from_value(0, ValueType::Nil);
                Some(Err(anyhow!("not list")))
            }
        }
    }
}

pub fn list_iterator(v: OpaqueValue) -> impl Iterator<Item=Result<OpaqueValue>> {
    ListIterator{current: v}
}

pub fn list_length(v: &OpaqueValue) -> Option<usize> {
    let mut current = v.clone();
    let mut current_size:usize = 0;
    loop {
        match current.get_obj() {
            Obj::Nil => {return Some(current_size)}
            Obj::Cons(cons) => {
                current_size+=1;
                current = cons.get_cdr()
            },
            _ => {return None}
        }
    }
}

pub fn list_nth(v: &OpaqueValue, idx: usize) -> Option<OpaqueValue> {
    match v.get_obj() {
        Obj::Cons(ref cons) => {
            if idx == 0 {
                Some(cons.get_car())
            } else {
                list_nth(&cons.get_cdr(), idx-1)
            }
        }
        _ => None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn can_get_i32() {
        let pool = ObjPool::new(100);
        let value = pool.get_i32(42);
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_get_nil() {
        let pool = ObjPool::new(100);
        let value = pool.get_nil();
        if let Obj::Nil = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_get_true() {
        let pool = ObjPool::new(100);
        let value = pool.get_true();
        if let Obj::True = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }#[test]
    fn can_get_false() {
        let pool = ObjPool::new(100);
        let value = pool.get_false();
        if let Obj::False = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }#[test]
    fn can_get_undef() {
        let pool = ObjPool::new(100);
        let value = pool.get_undef();
        if let Obj::Undef = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_alloc_string() {
        let mut pool = ObjPool::new(100);
        let value = pool.get_symbol("test").unwrap();
        if let Obj::Symbol(sym_idx) = value.get_obj() {
            assert_eq!(pool.get_symbol_str(sym_idx), "test".to_string())
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_alloc_cons() {
        let mut pool = ObjPool::new(100);
        let nil = pool.get_nil();
        let str = pool.get_symbol("test").unwrap();
        let value = pool.alloc_cons(str, nil).unwrap();
        if let Obj::Cons(cons) = value.get_obj() {
            if let Obj::Symbol(sym_idx) = cons.get_car().get_obj() {
                assert_eq!(pool.get_symbol_str(sym_idx), "test".to_string())
            } else {
                panic!("unexpected")
            }
            if let Obj::Nil = cons.get_cdr().get_obj() {
            } else {
                panic!("unexpected")
            }
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_alloc_closure() {
        let mut pool = ObjPool::new(100);
        let nil = pool.get_nil();
        let value = pool.alloc_closure(42, nil).unwrap();
        if let Obj::Closure(closure) = value.get_obj() {
            assert_eq!(42, closure.get_func_id());
            if let Obj::Nil = closure.get_env().get_obj() {
            } else {
                panic!("unexpected")
            }
        } else {
            panic!("unexpected")
        }
    }
}