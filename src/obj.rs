use std::collections::HashMap;
use std::alloc::{GlobalAlloc, System, Layout};
use std::fmt::Write;
use anyhow::{Result, anyhow};
use std::mem::size_of;

pub struct ObjPool {
    layout: Layout,
    alloced: *mut u8,
    ptr: *mut u8,
    end: *mut u8,
    symbols: Vec<String>,
    symbols_map: HashMap<String, SymbolId>,
}

#[repr(C)]
#[derive(Clone,Copy)]
enum ObjType {
    Cons,
}
enum ValueType {
    Nil,
    I32,
    Symbol,
    Native,
}

type Value = u64;
pub type NativeId = u32;
pub type SymbolId = u32;
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
            } else {
                panic!("unexpected value type {}", value_type)
            }
        } else {
            // pointer
            let ptr: *mut ObjHead = unsafe{ std::mem::transmute(self.0) };
            match unsafe { (*ptr).obj_type } {
                ObjType::Cons => Obj::Cons(OpaqueValueCons(self.0 as *mut ObjCons)),
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
pub enum Obj {
    Nil,
    I32(i32),
    Native(NativeId),
    Symbol(SymbolId),
    Cons(OpaqueValueCons),
}

impl Drop for ObjPool {
    fn drop(&mut self) {
        unsafe {System.dealloc(self.alloced, self.layout)}
    }
}

impl ObjPool {
    pub fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size, 8).unwrap();
        let ptr = unsafe { System.alloc(layout)};
        Self {
            layout,
            alloced: ptr,
            ptr,
            end: unsafe { ptr.add(size) },
            symbols: Vec::new(),
            symbols_map: HashMap::new(),
        }
    }
    unsafe fn alloc(&mut self, size: usize, value: u32, obj_type: ObjType) -> Result<* mut ObjHead> {
        let size = (size + 1) / 2 * 2;
        if self.ptr.add(size) >= self.end {
            return Err(anyhow!("no space left in pool"));
        }
        let ptr = self.ptr as *mut ObjHead;
        self.ptr = unsafe {self.ptr.add(size)};
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
        let ptr = unsafe { self.alloc(size_of::<ObjCons>(), 0, ObjType::Cons)? };
        unsafe {
            let ptr = ptr as *mut ObjCons;
            (*ptr).car = car.0;
            (*ptr).cdr = cdr.0;
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
            Obj::I32(i) => {write!(w, "{}",i)?;}
            Obj::Native(i) => {write!(w, "#native:{}#", i)?;}
            Obj::Symbol(s) => {write!(w, "{}", self.get_symbol_str(s))?;}
            Obj::Cons(_) => {self.write_list(w, v)?;}
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
}