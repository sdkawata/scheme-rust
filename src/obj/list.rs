use anyhow::{anyhow, Result};
use super::{OpaqueValue, Obj};

pub enum ElemOrTail {
    Elem(OpaqueValue),
    Tail(OpaqueValue),
}
impl ElemOrTail {
    pub fn expect_elem(self) -> Result<OpaqueValue> {
        match self {
            Self::Elem(v) => Ok(v),
           _ => Err(anyhow!("not list")),
        }
    }
}
pub struct ListIterator {
    current: OpaqueValue
}

impl Iterator for ListIterator {
    type Item = ElemOrTail;
    fn next(&mut self) -> Option<Self::Item> {
        match self.current.to_owned().get_obj() {
            Obj::Cons(cons) => {
                let car = cons.get_car();
                self.current = cons.get_cdr();
                Some(ElemOrTail::Elem(car))
            },
            Obj::Nil => None,
            _ => {
                let current = self.current.to_owned();
                self.current = super::get_nil();
                Some(ElemOrTail::Tail(current))
            }
        }
    }
}

impl ListIterator {
    pub fn current(self) -> OpaqueValue {
        self.current
    }
}

pub fn list_iterator(v: OpaqueValue) -> ListIterator {
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
    match v.to_owned().get_obj() {
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

pub fn list_skip_n(v: &OpaqueValue, n: usize) -> Option<OpaqueValue> {
    let mut iter = list_iterator(v.to_owned());
    for _ in 0..n {
        match iter.next() {
            Some(ElemOrTail::Elem(_)) => (),
            _ => {return None}
        }
    }
    Some(iter.current())
}