use std::cell::RefCell;
use std::char::from_u32_unchecked;
use std::alloc::{GlobalAlloc, System, Layout};
use std::io::Write;
use std::ptr::NonNull;
use anyhow::{Result, anyhow};
use std::mem::size_of;

use self::symbol::Symbol;

pub mod frame;
pub mod symbol;
pub mod list;

#[repr(C)]
#[derive(Clone,Copy, Debug, PartialEq, Eq)]
enum ObjType {
    Cons,
    Closure,
    Forwarded,
}

#[repr(u32)]
#[derive(Clone,Copy,Debug,PartialEq, Eq)]
enum ValueType {
    Nil = 0,
    I32,
    F32,
    True,
    False,
    Undef,
    Symbol,
    Native,
    Char,
}

type Value = u64;
pub type NativeId = u32;

pub type FuncId = u32;
#[repr(C)]
struct ObjHead {
    value: u32,
    obj_type: ObjType,
}

#[repr(C)]
struct ObjCons {
    head: ObjHead,
    car: RawValue,
    cdr: RawValue,
}

#[repr(C)]
struct ObjClosure {
    head: ObjHead,
    func_id: FuncId,
    env: RawValue,
}


#[repr(C)]
struct ObjForwarded {
    head: ObjHead,
    forwarded: RawValue,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct RawValue{
    value: Value
}

impl RawValue {
    unsafe fn from_objhead_ptr(ptr:*mut ObjHead) -> Self{
        RawValue{value: std::mem::transmute(ptr)}
    }
    fn from_value(value: u32, value_type: ValueType) -> Self {
        RawValue{value: ((value as u64) << 32) + ((value_type as u64) << 1) + 1}
    }
    #[inline]
    unsafe fn as_ptr<T>(&self) -> *mut T {
        std::mem::transmute(self.value)
    }
    #[inline]
    fn is_value(&self) -> bool {
        self.value %2 == 1
    }
    #[inline]
    fn is_nil(&self) -> bool {
        self.value == 1
    }
    #[inline]
    unsafe fn obj_type(&self) -> ObjType {
        debug_assert!(!self.is_value());
        let ptr: *mut ObjHead = self.as_ptr();
        unsafe {(*ptr).obj_type}
    }
    unsafe fn obj_size(&self) -> usize {
        debug_assert!(!self.is_value());
        match self.obj_type() {
            ObjType::Cons => size_of::<ObjCons>(),
            ObjType::Closure => size_of::<ObjClosure>(),
            ObjType::Forwarded => size_of::<ObjForwarded>(),
        }
    }
    #[inline]
    unsafe fn value(&self) -> u32 {
        debug_assert!(self.is_value());
        (self.value >> 32) as u32
    }
    #[inline]
    unsafe fn value_type_u32(&self) -> u32 {
        debug_assert!(self.is_value());
        ((self.value & 0xffff) >> 1) as u32
    }
    #[inline]
    unsafe fn value_type(&self) -> ValueType {
        std::mem::transmute(self.value_type_u32())
    }
}

impl From<Ptr> for RawValue {
    fn from(item: Ptr) -> RawValue {
       item.get_raw_value()
    }
}

impl From<OpaqueValue> for RawValue {
    fn from(item: OpaqueValue) -> RawValue {
        item.as_raw_value()
    } 
}

#[derive(Clone)]
enum ValueOrPtr {
    Value(RawValue),
    Ptr(Ptr)
}

#[derive(Clone)]
pub struct OpaqueValue(ValueOrPtr);

impl OpaqueValue {
    #[inline]
    pub fn get_obj(self) -> Obj {
        match self.0 {
            ValueOrPtr::Value(raw_value) => {
                let value = unsafe { raw_value.value() };
                let value_type = unsafe { raw_value.value_type() };
                match value_type {
                    ValueType::I32 => Obj::I32(value as i32),
                    ValueType::F32 => Obj::F32(unsafe {std::mem::transmute(value)}),
                    ValueType::Nil => Obj::Nil,
                    ValueType::Symbol => Obj::Symbol(Symbol(value as symbol::SymbolId)),
                    ValueType::Native => Obj::Native(value),
                    ValueType::True => Obj::True,
                    ValueType::False => Obj::False,
                    ValueType::Undef => Obj::Undef,
                    ValueType::Char => Obj::Char(unsafe{ from_u32_unchecked(value) }),
                }
            },
            ValueOrPtr::Ptr(ptr) => {
                match unsafe {ptr.get_raw_value().obj_type() } {
                    ObjType::Cons => Obj::Cons(OpaqueValueCons(ptr)),
                    ObjType::Closure => Obj::Closure(OpaqueValueClosure(ptr)),
                    ObjType::Forwarded => Obj::Forwarded(OpaqueValueForwarded(ptr)),
                }
            }
        }
    }
    fn is_value_type(&self, value_type: ValueType) -> bool {
        if let ValueOrPtr::Value(v) = self.0 {
            if unsafe {v.value_type()} == value_type {
                true
            } else {
                false
            }
        } else {
            false
        }
    }
    pub fn is_i32(&self) -> bool {
        self.is_value_type(ValueType::I32)
    }
    pub fn is_f32(&self) -> bool {
        self.is_value_type(ValueType::F32)
    }
    pub fn is_nil(&self) -> bool {
        self.is_value_type(ValueType::Nil)
    }
    fn as_raw_value(&self) -> RawValue {
        match &self.0 {
            ValueOrPtr::Value(value) => *value,
            ValueOrPtr::Ptr(ptr) => ptr.get_raw_value(),
        }
    }
}

impl From<RawValue> for OpaqueValue {
    fn from(item: RawValue) -> OpaqueValue {
        if item.is_value() {
            OpaqueValue(ValueOrPtr::Value(item))
        } else {
            OpaqueValue(ValueOrPtr::Ptr(item.into()))
        }
    }
}


#[derive(Clone)]
pub struct OpaqueValueCons(Ptr);

impl OpaqueValueCons {
    unsafe fn as_ptr(&self) -> *mut ObjCons {
        self.0.get_raw_value().as_ptr::<ObjCons>()
    }
    pub fn set_car(&self, v: OpaqueValue) {
        unsafe {(*self.as_ptr()).car = v.into();}
    }
    pub fn set_cdr(&self, v: OpaqueValue) {
        unsafe {(*self.as_ptr()).cdr = v.into();}
    }
    pub fn get_car(&self) -> OpaqueValue {
        unsafe {(*self.as_ptr()).car}.into()
    }
    pub fn get_cdr(&self) -> OpaqueValue {
        unsafe {(*self.as_ptr()).cdr}.into()
    }
}


#[derive(Clone)]
pub struct OpaqueValueForwarded(Ptr);

#[derive(Clone)]
pub struct OpaqueValueClosure(Ptr);

impl OpaqueValueClosure {
    unsafe fn as_ptr(&self) -> *mut ObjClosure {
       self.0.get_raw_value().as_ptr::<ObjClosure>()
    }
    pub fn get_func_id(&self) -> FuncId {
        unsafe {(*self.as_ptr()).func_id}
    }
    pub fn get_env(&self) -> OpaqueValue {
        unsafe {(*self.as_ptr()).env}.into()
    }
}

#[derive(Clone)]
pub enum Obj {
    Nil,
    True,
    False,
    Undef,
    I32(i32),
    F32(f32),
    Char(char),
    Native(NativeId),
    Symbol(Symbol),
    Cons(OpaqueValueCons),
    Closure(OpaqueValueClosure),
    Forwarded(OpaqueValueForwarded),
}

struct PtrNode {
    next: Option<NonNull<PtrNode>>,
    prev: Option<NonNull<PtrNode>>,
    value: RawValue,
}

impl PtrNode {
    fn new_ptr(value: RawValue) -> NonNull<PtrNode> {
        Box::leak(
            Box::new(
                PtrNode {
                    prev: None,
                    next: None,
                    value: value,
                }
            )
        ).into()
    }
}

pub struct Ptr(NonNull<PtrNode>);

impl Ptr {
    fn get_raw_value(&self) -> RawValue {
        unsafe { (*self.0.as_ptr()).value}
    }
}

impl From<RawValue> for Ptr {
    fn from(item: RawValue) -> Ptr {
        OBJ_POOL.with(|obj_pool| obj_pool.borrow_mut().ptr(item))
    }
}

impl Drop for Ptr {
    fn drop(&mut self) {
        unsafe {
            let prev = (*self.0.as_ptr()).prev;
            let next = (*self.0.as_ptr()).next;
            if let Some(prev_node_ptr) = prev {
                (*prev_node_ptr.as_ptr()).next = next;
            }
            if let Some(next_node_ptr) = next {
                (*next_node_ptr.as_ptr()).prev = prev;
            }
            let _ = Box::from_raw(self.0.as_ptr()); // free ptr
        }
    }
}

impl Clone for Ptr {
    fn clone(&self) -> Self {
        self.get_raw_value().into()
    }
}

thread_local! {static OBJ_POOL:RefCell<ObjPool> = RefCell::new(ObjPool::new(100000))}
struct ObjPool {
    layout: Layout,
    alloced: *mut u8,
    current: *mut u8,
    from_space: *mut u8,
    to_space: *mut u8,
    pool_size: usize,
    head_entry: NonNull<PtrNode>,
    tail_entry: NonNull<PtrNode>,
    pub disable_gc: bool,
    pub force_gc_every_alloc: bool,
}


impl Drop for ObjPool {
    fn drop(&mut self) {
        unsafe {System.dealloc(self.alloced, self.layout)}
    }
}

impl ObjPool {
    pub fn new(size: usize) -> Self {
        let layout = Layout::from_size_align(size * 2, 8).unwrap();
        let ptr = unsafe { System.alloc(layout)};
        let head_entry: NonNull<PtrNode> = PtrNode::new_ptr(get_nil().into());
        let tail_entry: NonNull<PtrNode> = PtrNode::new_ptr(get_nil().into());
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
            head_entry,
            tail_entry,
            disable_gc: false,
            force_gc_every_alloc: false,
        }
    }
    fn ptr(&mut self, value: RawValue) -> Ptr {
        //eprintln!("from_space:{:?} to_space:{:?} pool_size:{} ptr:{:?}", self.from_space, self.to_space,self.pool_size, value.as_ptr());
        debug_assert!(unsafe{ value.is_value() || (value.as_ptr::<u8>()) >= self.from_space});
        debug_assert!(unsafe{ value.is_value() || (value.as_ptr::<u8>()) < self.from_space.add(self.pool_size) });
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
    unsafe fn init_obj_head(&self, ptr: *mut ObjHead, value: u32, obj_type: ObjType) {
        (*ptr).value = value;
        (*ptr).obj_type = obj_type;
    }
    unsafe fn no_space_left(&self, size: usize) -> bool {
        self.current.add(size) >= self.from_space.add(self.pool_size)
    }
    unsafe fn alloc(&mut self, size: usize, value: u32, obj_type: ObjType) -> Result<* mut ObjHead> {
        // let size = (size + 1) / 2 * 2;
        if ! self.disable_gc && (self.force_gc_every_alloc ||  self.no_space_left(size)) {
            self.start_gc();
        }
        if self.no_space_left(size) {
            return Err(anyhow!("no space left in pool"));
        }
        let ptr = self.current as *mut ObjHead;
        self.current = unsafe {self.current.add(size)};
        self.init_obj_head(ptr, value, obj_type);
        Ok(ptr)
    }
    unsafe fn copy_obj(&mut self, value: RawValue) -> RawValue {
        if value.is_value() {
            return value;
        }
        //eprintln!("copy_obj ptr:{:?} current:{:?} type:{:?} size:{} obj:{}", value.as_ptr(), self.current, value.obj_type(), value.obj_size(), self.write_to_string(&value));
        debug_assert!(unsafe{(value.as_ptr::<u8>()) >= self.to_space});
        debug_assert!(unsafe{(value.as_ptr::<u8>()) < self.to_space.add(self.pool_size)});
        match value.obj_type() {
            ObjType::Forwarded => {
                (*value.as_ptr::<ObjForwarded>()).forwarded
            },
            _ => {
                let forwarded_addr = self.current;
                self.current = self.current.add(value.obj_size());
                std::ptr::copy_nonoverlapping(value.as_ptr() as *mut u8, forwarded_addr, value.obj_size());
                self.init_obj_head(value.as_ptr(), 0, ObjType::Forwarded);
                let forwarded = RawValue::from_objhead_ptr(forwarded_addr as *mut ObjHead);
                (*value.as_ptr::<ObjForwarded>()).forwarded = forwarded;
                forwarded
            }
        }
    }
    unsafe fn start_gc(&mut self) {
        //eprintln!("start_gc");
        std::mem::swap(&mut self.to_space, &mut self.from_space);
        self.current = self.from_space;
        //eprintln!("start_gc from_space:{:?} to_space:{:?}", self.from_space, self.to_space);
        let mut scan_ptr = self.current;
        let mut current_entry = Some(self.head_entry);
        while let Some(entry) = current_entry {
            // eprintln!("ptr:{:?}", (*entry.as_ptr()).element.as_ptr());
            (*entry.as_ptr()).value = self.copy_obj((*entry.as_ptr()).value);
            current_entry = (*entry.as_ptr()).next;
        }
        while scan_ptr < self.current {
            let current_value = RawValue::from_objhead_ptr(scan_ptr as *mut ObjHead);
            //eprintln!("scan {:?} current:{:?} type:{:?} {}", scan_ptr, self.current, current_value.obj_type(), self.write_to_string(&current_value));
            match current_value.obj_type() {
                ObjType::Cons => {
                    let ptr = current_value.as_ptr::<ObjCons>();
                    (*ptr).car = self.copy_obj((*ptr).car);
                    (*ptr).cdr = self.copy_obj((*ptr).cdr);
                },
                ObjType::Closure => {
                    let ptr = current_value.as_ptr::<ObjClosure>();
                    (*ptr).env = self.copy_obj((*ptr).env)
                }
                _ => panic!("unreachable")
            }
            scan_ptr = scan_ptr.add(current_value.obj_size())
        }
        //eprintln!("end_gc current_size:{}", self.current as usize - self.from_space as usize);
    }
}


pub fn get_i32(i: i32) -> OpaqueValue {
    RawValue::from_value(i as u32, ValueType::I32).into()
}
pub fn get_f32(f: f32) -> OpaqueValue {
    RawValue::from_value(unsafe {std::mem::transmute(f)}, ValueType::F32).into()
}
pub fn get_char(c: char) -> OpaqueValue {
    RawValue::from_value(c as u32, ValueType::Char).into()
}
pub fn get_symbol(s: Symbol) -> OpaqueValue {
    RawValue::from_value(s.0 as u32, ValueType::Symbol).into()
}
pub fn get_symbol_from_str(s: &str) -> OpaqueValue {
    RawValue::from_value(symbol::from_str(s).0 as u32, ValueType::Symbol).into()
}
pub fn get_native(i: NativeId) -> OpaqueValue {
    RawValue::from_value(i as u32, ValueType::Native).into()
}
pub fn get_nil() -> OpaqueValue {
    get_raw_nil().into()
}
fn get_raw_nil() -> RawValue {
    RawValue::from_value(0, ValueType::Nil)
}
pub fn get_true() -> OpaqueValue {
    RawValue::from_value(0, ValueType::True).into()
}
pub fn get_false() -> OpaqueValue {
    RawValue::from_value(0, ValueType::False).into()
}
pub fn get_undef() -> OpaqueValue {
    RawValue::from_value(0, ValueType::Undef).into()
}


pub fn alloc_cons(car: OpaqueValue, cdr: OpaqueValue) -> Result<OpaqueValue> {
    OBJ_POOL.with(|obj_pool| {
        unsafe {
            let ptr = obj_pool.borrow_mut().alloc(size_of::<ObjCons>(), 0, ObjType::Cons)?;
            {
                let ptr = ptr as *mut ObjCons;
                (*ptr).car = car.into();
                (*ptr).cdr = cdr.into();
            }
            Ok(RawValue::from_objhead_ptr(ptr).into())
        }
    })
}
pub fn alloc_closure(func_id: FuncId, env: OpaqueValue) -> Result<OpaqueValue> {
    OBJ_POOL.with(|obj_pool| {
        unsafe {
            let ptr = obj_pool.borrow_mut().alloc(size_of::<ObjClosure>(), 0, ObjType::Closure)?;
            {
                let ptr = ptr as *mut ObjClosure;
                (*ptr).func_id = func_id;
                (*ptr).env = env.into();
            }
            Ok(RawValue::from_objhead_ptr(ptr).into())
        }
    })
}

pub fn display_to_string(v: &OpaqueValue) -> String {
    display_to_string_internal(v, true)
}
pub fn write_to_string(v: &OpaqueValue) -> String {
    display_to_string_internal(v, false)
}
fn display_to_string_internal(v: &OpaqueValue, display: bool) -> String{
    let mut buf = Vec::<u8>::new();
    display_internal(&mut buf, v, display).unwrap();
    String::from_utf8(buf).unwrap()
}
pub fn display<W:Write>(w: &mut W, v: &OpaqueValue) -> Result<()> {
    display_internal(w, v, true)
}
pub fn write<W:Write>(w: &mut W, v: &OpaqueValue) -> Result<()> {
    display_internal(w, v, true)
}

fn display_internal<W:Write>(w: &mut W, v: &OpaqueValue, display: bool) -> Result<()> {
    match v.clone().get_obj() {
        Obj::Nil => {write!(w, "()")?;}
        Obj::True => {write!(w, "#t")?;}
        Obj::False => {write!(w, "#f")?;}
        Obj::Undef => {write!(w, "#undef")?;}
        Obj::I32(i) => {write!(w, "{}",i)?;}
        Obj::F32(f) => {write!(w, "{}",f)?;}
        Obj::Char(c) => {
            if display {
                write!(w, "{}", c)?;
            } else {
                write!(w, "#\\{}", c)?;
            }
        }
        Obj::Native(i) => {write!(w, "#native:{}#", i)?;}
        Obj::Symbol(s) => {write!(w, "{}", s.as_str())?;}
        Obj::Cons(_) => {display_list(w, v)?;}
        Obj::Closure(_) => {write!(w, "#closure#")?;}
        Obj::Forwarded(_) => {write!(w, "#forwarded#")?;}
    }
    Ok(())
}
fn display_list<W:Write>(w: &mut W, v: &OpaqueValue) -> Result<()> {
    write!(w, "(")?;
    let mut current: OpaqueValue = v.to_owned();
    let mut first = true;
    loop {
        match current.clone().get_obj() {
            Obj::Cons(cons) => {
                if !first {
                    write!(w, " ")?;
                }
                first = false;
                display(w, &cons.get_car())?;
                current = cons.get_cdr();
            },
            Obj::Nil => {break}
            _ => {
                write!(w, ". ")?;
                display(w, &current)?;
                break
            }
        }
    }
    write!(w, ")")?;
    Ok(())
}

pub fn set_disable_gc(disable_gc: bool) {
    OBJ_POOL.with(|obj_pool| obj_pool.borrow_mut().disable_gc = disable_gc )
}
pub fn set_force_gc_every_alloc(force_gc_every_alloc: bool) {
    OBJ_POOL.with(|obj_pool| obj_pool.borrow_mut().force_gc_every_alloc = force_gc_every_alloc )
}

pub fn equal(v1: &OpaqueValue, v2: &OpaqueValue) -> bool {
    match (v1.to_owned().get_obj(), v2.to_owned().get_obj()) {
        (Obj::True, Obj::True) => true,
        (Obj::False, Obj::False) => true,
        (Obj::Undef, Obj::Undef) => true,
        (Obj::I32(i1), Obj::I32(i2)) => i1 == i2,
        (Obj::F32(f1), Obj::F32(f2)) => f1 == f2,
        (Obj::Char(c1), Obj::Char(c2)) => c1 == c2,
        (Obj::Nil, Obj::Nil) => true,
        (Obj::Symbol(s1), Obj::Symbol(s2)) => s1 == s2,
        (Obj::Cons(c1), Obj::Cons(c2)) => equal(&c1.get_car(), &c2.get_car()) && equal(&c1.get_car(), &c2.get_car()),
        _ => false,
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn can_get_i32() {
        let value = get_i32(42);
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_get_nil() {
        let value = get_nil();
        if let Obj::Nil = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_get_true() {
        let value = get_true();
        if let Obj::True = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }#[test]
    fn can_get_false() {
        let value = get_false();
        if let Obj::False = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }#[test]
    fn can_get_undef() {
        let value = get_undef();
        if let Obj::Undef = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_alloc_string() {
        let value = get_symbol_from_str("test");
        if let Obj::Symbol(s) = value.get_obj() {
            assert_eq!(s.as_str(), "test".to_string())
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn can_alloc_cons() {
        let nil = get_nil();
        let str = get_symbol_from_str("test");
        let value = alloc_cons(str, nil).unwrap();
        if let Obj::Cons(cons) = value.get_obj() {
            if let Obj::Symbol(s) = cons.get_car().get_obj() {
                assert_eq!(s.as_str(), "test".to_string())
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
        let nil = get_nil();
        let value = alloc_closure(42, nil).unwrap();
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