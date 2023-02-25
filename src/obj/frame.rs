use super::*;
use anyhow::Result;

pub fn extend_frame(frame: &OpaqueValue) -> Result<OpaqueValue> {
    Ok(alloc_cons(get_nil(), frame.clone())?)
}

pub fn lookup(s: SymbolId, frame: &OpaqueValue) -> Option<OpaqueValue> {
    // eprintln!("frame:{}", write_to_string(frame));
    unsafe {
        let mut current_frame: RawValue = frame.as_raw_value();
        loop {
            if current_frame.is_nil() {
                break;
            }
            if ! current_frame.is_value() && current_frame.obj_type() == ObjType::Cons {
                let ptr = current_frame.as_ptr::<ObjCons>();
                let mut pair_list = (*ptr).car;
                loop {
                    if pair_list.is_nil() {
                        break;
                    }
                    if ! pair_list.is_value() && pair_list.obj_type() == ObjType::Cons {
                        let ptr = pair_list.as_ptr::<ObjCons>();
                        let pair = (*ptr).car;
                        if ! pair.is_value() && pair.obj_type() == ObjType::Cons {
                            let ptr = pair.as_ptr::<ObjCons>();
                            let car = (*ptr).car;
                            if car.is_value() && car.value_type() == ValueType::Symbol {
                                if car.value() == s {
                                    return Some((*ptr).cdr.into())
                                }
                            } else {
                                panic!("internal error: unexpected environment format: car of pair is not symbol")
                            }
                        }
                        pair_list = (*ptr).cdr;
                    } else {
                        panic!("internal error: unexpected environment format: pair_list is not list")
                    }
                }
                current_frame = (*ptr).cdr;
            } else {
                panic!("internal error: unexpected environment format: frame is not list")
            }
        }
        None
    }
}

pub fn add_new_var(frame: OpaqueValue, s: SymbolId, v: OpaqueValue) -> Result<()> {
    if let Obj::Cons(cons) = frame.clone().get_obj() {
        let top_frame = cons.get_car();
        let new_pair = alloc_cons(get_symbol_from_idx(s), v)?;
        let new_top_frame = alloc_cons(new_pair, top_frame)?;
        cons.set_car(new_top_frame);
        // println!("env: {}", pool.write_to_string(&self.current_env));
        Ok(())
    } else {
        panic!("unexpected environment format: not cons")
    }
}

pub fn set_var(frame: OpaqueValue, s: SymbolId, v: OpaqueValue) -> Result<()> {
    for frame in list_iterator(frame.clone()) {
        let frame = frame.unwrap();
        for pair in list_iterator(frame) {
            if let Obj::Cons(cons) = pair.unwrap().get_obj() {
                if let Obj::Symbol(symbol_id) = cons.get_car().get_obj() {
                    if symbol_id == s {
                        cons.set_cdr(v);
                        return Ok(())
                    }
                } else {
                    panic!("internal error:unexpected environment format:car of pair is not symbol")
                }
            } else {
                panic!("internal error: unexpected environment format: frame is not list")
            }
        }
    }
    Err(anyhow!("cannot set var: not found"))
}
pub fn previous_frame(frame: OpaqueValue) -> Result<OpaqueValue> {
    if let Obj::Cons(cons) = frame.get_obj() {
        Ok(cons.get_car())
    } else {
        panic!("unexpected environment format: not cons")
    }
}