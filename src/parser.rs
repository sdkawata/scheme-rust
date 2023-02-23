use std::collections::VecDeque;
use anyhow::Result;
use crate::obj::{ObjPool,OpaqueValue};

peg::parser!{
    grammar scheme_parser() for str {
        rule number(pool: &mut ObjPool) -> Result<OpaqueValue>
            = n:$(['0'..='9'] ['0'..='9']*) { Ok(pool.get_i32(n.parse()?))}
        rule true_value(pool: &mut ObjPool) -> Result<OpaqueValue>
            = "#t" {Ok(pool.get_true())}
        rule false_value(pool: &mut ObjPool) -> Result<OpaqueValue>
            = "#f" {Ok(pool.get_false())}
        rule _ -> () = [' ' | '\r' | '\n']* {()}
        rule list(pool: &mut ObjPool)  -> Result<OpaqueValue> 
            = "(" _ l:(value(pool) ** _) _ ")" {
                let mut reversed = VecDeque::<OpaqueValue>::new();
                for v in l {
                    reversed.push_front(v?)
                }
                let mut res = pool.get_nil();
                for v in reversed {
                    res = pool.alloc_cons(v, res)?
                }
                Ok(res)
            }
        rule symbol(pool: &mut ObjPool) -> Result<OpaqueValue>
            = s:$(['a'..='z' | '+' | '=' | '?']+) {Ok(pool.get_symbol(s)?)}
        rule quoted(pool: &mut ObjPool) -> Result<OpaqueValue> 
            = "'" _ v:value(pool) {
                let quote_symbol_idx = pool.get_symbol_idx("quote");
                let cons = pool.alloc_cons(
                    v?,
                    pool.get_nil()
                )?;
                Ok(
                    pool.alloc_cons(pool.get_symbol_from_idx(quote_symbol_idx), cons)?
                )
            }
        rule value(pool: &mut ObjPool) -> Result<OpaqueValue>
            = n:(number(pool) / list(pool) / symbol(pool) / true_value(pool) / false_value(pool) / quoted(pool)) {n}
        pub rule top(pool: &mut ObjPool) -> Result<OpaqueValue>
            = _ n:value(pool) _ {n}
    }
}

pub fn parse(s: &str, pool: &mut ObjPool) -> Result<OpaqueValue> {
    // Err(anyhow!("a"))
    scheme_parser::top(s, pool)?
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::obj::{ObjPool,Obj};
    #[test]
    fn parse_number() {
        let mut obj = ObjPool::new(100);
        let value = parse("42", &mut obj).unwrap();
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_true() {
        let mut obj = ObjPool::new(100);
        let value = parse("#t", &mut obj).unwrap();
        if let Obj::True = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }#[test]
    fn parse_false() {
        let mut obj = ObjPool::new(100);
        let value = parse("#f", &mut obj).unwrap();
        if let Obj::False = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_number_with_space() {
        let mut obj = ObjPool::new(100);
        let value = parse(" 42 ", &mut obj).unwrap();
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_symbol() {
        let mut pool = ObjPool::new(100);
        let value = parse("if", &mut pool).unwrap();
        if let Obj::Symbol(sym_idx) = value.get_obj() {
            assert_eq!("if", pool.get_symbol_str(sym_idx))
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_list() {
        let mut pool = ObjPool::new(100);
        let value = parse("(if 2)", &mut pool).unwrap();
        if let Obj::Cons(cons) = value.get_obj() {
            if let Obj::Symbol(sym_idx) = cons.get_car().get_obj() {  
                assert_eq!("if", pool.get_symbol_str(sym_idx))
            } else {panic!("unexpected")}
            if let Obj::Cons(cons2) = cons.get_cdr().get_obj() {  
                if let Obj::I32(2) = cons2.get_car().get_obj() {} else {panic!("unexpected")}
                if let Obj::Nil = cons2.get_cdr().get_obj() {} else {panic!("unexpected")}
            } else {panic!("unexpected")}
        } else {
            panic!("unexpected")
        }
    }
}