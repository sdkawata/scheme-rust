use std::alloc::{GlobalAlloc, System, Layout};
use anyhow::{Result, anyhow};
use std::mem::size_of;

pub struct ObjPool {
    ptr: *mut u8,
    end: *mut u8,
}

#[repr(C)]
#[derive(Clone,Copy)]
enum ObjType {
    Symbol,
    Cons,
}
enum ValueType {
    Nil,
    I32,
}

type Value = u64;
#[repr(C)]
struct ObjHead {
    value: u32,
    obj_type: ObjType,
}

#[repr(C)]
struct ObjSymbol {
    // value = len
    head: ObjHead,
}
#[repr(C)]
struct ObjCons {
    head: ObjHead,
    car: u64,
    cdr: u64,
}

#[repr(C)]
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
            } else {
                panic!("unexpected value type {}", value_type)
            }
        } else {
            // pointer
            let ptr: *mut ObjHead = unsafe{ std::mem::transmute(self.0) };
            match unsafe { (*ptr).obj_type } {
                ObjType::Symbol => Obj::Symbol(OpaqueValueSymbol(self.0 as *mut ObjSymbol)),
                ObjType::Cons => Obj::Cons(OpaqueValueCons(self.0 as *mut ObjCons)),
            }
        }
    }
}

pub struct OpaqueValueCons(*mut ObjCons);

impl OpaqueValueCons {
    fn get_car(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0).car})
    }
    fn get_cdr(&self) -> OpaqueValue {
        OpaqueValue(unsafe {(*self.0).cdr})
    }
}
pub struct OpaqueValueSymbol(*mut ObjSymbol);

impl OpaqueValueSymbol {
    fn get_string(&self) -> String {
        let len = unsafe {(*self.0).head.value} as usize;
        let slice = unsafe {
            std::slice::from_raw_parts((self.0 as *mut u8).add(size_of::<ObjSymbol>()), len)
        };
        let mut vec = Vec::<u8>::with_capacity(len);
        for b in slice {
            vec.push(*b);
        }
        String::from_utf8(vec).unwrap()
    }
}

pub enum Obj {
    Nil,
    I32(i32),
    Symbol(OpaqueValueSymbol),
    Cons(OpaqueValueCons),
}

impl ObjPool {
    pub fn new(size: usize) -> Self {
        let ptr = unsafe { System.alloc(Layout::from_size_align(size, 8).unwrap())};
        Self {
            ptr,
            end: unsafe { ptr.add(size) },
        }
    }
    unsafe fn alloc_head(&mut self, value: u32, obj_type: ObjType) -> Result<*mut ObjHead> {
        self.alloc(size_of::<ObjHead>(), value, obj_type)
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
    pub fn get_nil(&self) -> OpaqueValue {
        OpaqueValue::from_value(0, ValueType::Nil)
    }
    pub fn alloc_symbol(&mut self, str: &str) -> Result<OpaqueValue> {
        let size = size_of::<ObjSymbol>() + str.len();
        let ptr = unsafe { self.alloc(size, str.len() as u32, ObjType::Symbol)? };
        unsafe {
            let ptr = ptr as *mut ObjSymbol;
            std::ptr::copy_nonoverlapping(str.as_ptr(), (ptr as *mut u8).add(size_of::<ObjSymbol>()), str.len())
        }
        Ok(OpaqueValue::from_objhead_ptr(ptr))
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
}

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
    let value = pool.alloc_symbol("test").unwrap();
    if let Obj::Symbol(symbol) = value.get_obj() {
        assert_eq!(symbol.get_string(), "test".to_string())
    } else {
        panic!("unexpected")
    }
}
#[test]
fn can_alloc_cons() {
    let mut pool = ObjPool::new(100);
    let nil = pool.get_nil();
    let str = pool.alloc_symbol("test").unwrap();
    let value = pool.alloc_cons(str, nil).unwrap();
    if let Obj::Cons(cons) = value.get_obj() {
        if let Obj::Symbol(symbol) = cons.get_car().get_obj() {
            assert_eq!(symbol.get_string(), "test".to_string())
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