use std::collections::VecDeque;
use anyhow::{anyhow, Result};
use crate::obj;
use crate::obj::{OpaqueValue};

const CHAR_MAP : & [(&str, char)] = &[
    ("space", ' '),
    ("newline", '\n'),
];

pub fn parse_char(s: &str) -> Result<char> {
    for (str, c) in CHAR_MAP {
        if s == *str {
            return Ok(*c)
        }
    }
    Err(anyhow!("char parse failed"))
}

peg::parser!{
    grammar scheme_parser() for str {
        rule number() -> Result<OpaqueValue>
            = n:$(['0'..='9'] ['0'..='9']*) { Ok(obj::get_i32(n.parse()?))}
        rule float() -> Result<OpaqueValue>
            = n:$(['0'..='9']+ "." ['0'..='9']*) { Ok(obj::get_f32(n.parse()?))}
        rule true_value() -> Result<OpaqueValue>
            = "#t" {Ok(obj::get_true())}
        rule false_value() -> Result<OpaqueValue>
            = "#f" {Ok(obj::get_false())}
        rule comment() -> () = ";" (!"\n" [_])* ['\n'] {()}
        rule _ -> () = ([' ' | '\r' | '\n'] / comment())* {()}
        rule char_by_single_char() -> Result<OpaqueValue> = "#\\" c:([_]) {
            Ok(obj::get_char(c))
        }
        rule char_by_multiple_char() -> Result<OpaqueValue> = "#\\" s:(['a'..='z' | 'A'..='Z' | '0'..='9']+) {
            if s.len() == 1 {
                Ok(obj::get_char(s[0]))
            } else {
                Ok(obj::get_char(super::parse_char(&s.iter().collect::<String>())?))
            }
        }
        rule char() -> Result<OpaqueValue> = c:(char_by_multiple_char() / char_by_single_char()) {c}
        rule list()  -> Result<OpaqueValue> 
            = "(" _ l:(value() ** _) _ ")" {
                let mut reversed = VecDeque::<OpaqueValue>::new();
                for v in l {
                    reversed.push_front(v?)
                }
                let mut res = obj::get_nil();
                for v in reversed {
                    res = obj::alloc_cons(v, res)?
                }
                Ok(res)
            }
        rule symbol() -> Result<OpaqueValue>
            = s:$(['a'..='z' | '+' | '=' | '?' | '-' | '_' | '*' | '/']+) {Ok(obj::get_symbol(s)?)}
        rule quoted() -> Result<OpaqueValue> 
            = "'" _ v:value() {
                let quote_symbol_idx = obj::get_symbol_idx("quote");
                let cons = obj::alloc_cons(
                    v?,
                    obj::get_nil()
                )?;
                Ok(
                    obj::alloc_cons(obj::get_symbol_from_idx(quote_symbol_idx), cons)?
                )
            }
        rule value() -> Result<OpaqueValue>
            = n:(float() / number() / list() / symbol() / true_value() / false_value() / char() / quoted()) {n}
        pub rule values() -> Result<Vec<OpaqueValue>> 
            = _ l:(value() ** _) _ {l.into_iter().collect()}
        pub rule top() -> Result<OpaqueValue>
            = _ n:value() _ {n}
    }
}

pub fn parse(s: &str) -> Result<OpaqueValue> {
    // Err(anyhow!("a"))
    obj::set_disable_gc(true);
    let ret = scheme_parser::top(s)?;
    obj::set_disable_gc(false);
    ret
}
pub fn parse_values(s: &str) -> Result<Vec<OpaqueValue>> {
    obj::set_disable_gc(true);
    let ret = scheme_parser::values(s)?;
    obj::set_disable_gc(false);
    ret
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::obj::{Obj};
    #[test]
    fn parse_number() {
        let value = parse("42").unwrap();
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_true() {
        let value = parse("#t").unwrap();
        if let Obj::True = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_false() {
        let value = parse("#f").unwrap();
        if let Obj::False = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_char() {
        let value = parse("#\\a").unwrap();
        if let Obj::Char(c) = value.get_obj() {
            assert_eq!('a', c)
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_char_unicode() {
        let value = parse("#\\あ").unwrap();
        if let Obj::Char(c) = value.get_obj() {
            assert_eq!('あ', c)
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_char_name() {
        let value = parse("#\\space").unwrap();
        if let Obj::Char(c) = value.get_obj() {
            assert_eq!(' ', c)
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_number_with_space() {
        let value = parse(" 42 ").unwrap();
        if let Obj::I32(42) = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_nil_with_comment() {
        let value = parse(" (; this is comment \n ) ").unwrap();
        if let Obj::Nil = value.get_obj() {
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_symbol() {
        let value = parse("if").unwrap();
        if let Obj::Symbol(sym_idx) = value.get_obj() {
            assert_eq!("if", obj::get_symbol_str(sym_idx))
        } else {
            panic!("unexpected")
        }
    }
    #[test]
    fn parse_list() {
        let value = parse("(if 2)").unwrap();
        if let Obj::Cons(cons) = value.get_obj() {
            if let Obj::Symbol(sym_idx) = cons.get_car().get_obj() {  
                assert_eq!("if", obj::get_symbol_str(sym_idx))
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