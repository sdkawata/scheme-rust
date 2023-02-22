use crate::obj::{ObjPool, OpaqueValue, Obj, SymbolId, list_iterator, list_nth, list_length};
use anyhow::{Result, anyhow};

#[derive(Debug)]
enum OpCode {
    PushI32(i32), // stack: -> I32,
    PushNil, // stack: -> nil
    LookUp(SymbolId), // stack: -> Value
    PushNewVar(SymbolId), // stack: Value ->
    CreateNewFrame, 
    SetFramePrevious,
    Call, // stack: func args -> retval
    Cons, // stack: car cdr -> cons
    Ret, // stack: Retval -> 
}

struct Func {
    opcodes: Vec<OpCode>,
}

pub struct Environment {
    pool: ObjPool,
    funcs: Vec<Func>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            pool: ObjPool::new(1000000),
            funcs: Vec::new(),
        }
    }
    pub fn get_pool(&mut self) -> &mut ObjPool {
        &mut self.pool
    }
    pub fn emit(&mut self, v: &OpaqueValue) -> Result<usize> {
        let mut opcodes = Vec::new();
        self.emit_rec(&mut opcodes, v)?;
        opcodes.push(OpCode::Ret);
        let idx = self.funcs.len();
        // println!("{:?}", &opcodes);
        self.funcs.push(Func{
            opcodes
        });
        Ok(idx)
    }
    fn emit_cons(&mut self, opcodes: &mut Vec<OpCode>, v:&OpaqueValue) -> Result<()> {
        match v.get_obj() {
            Obj::Cons(cons) => {
                self.emit_rec(opcodes, &cons.get_car())?;
                self.emit_cons(opcodes, &cons.get_cdr())?;
                opcodes.push(OpCode::Cons);
                Ok(())
            },
            Obj::Nil => {
                opcodes.push(OpCode::PushNil);
                Ok(())
            }
            _ => Err(anyhow!("expected list: non-list given"))
        }
    }
    fn emit_rec(&mut self, opcodes: &mut Vec<OpCode>, v: &OpaqueValue) -> Result<()> {
        match v.get_obj() {
            Obj::I32(i) => {
                opcodes.push(OpCode::PushI32(i));
                Ok(())
            },
            Obj::Symbol(s) => {
                opcodes.push(OpCode::LookUp(s));
                Ok(())
            },
            Obj::Cons(cons) => {
                let car = cons.get_car();
                match car.get_obj() {
                    Obj::Symbol(s) if self.pool.get_symbol_str(s) == "let" => {
                        let length = list_length(v).ok_or(anyhow!("malformed let: not list"))?;
                        if length < 3 {
                            Err(anyhow!("malformed let: length < 3"))?;
                        }
                        let binds = list_nth(v, 1).unwrap();
                        opcodes.push(OpCode::CreateNewFrame);
                        for bind in list_iterator(binds) {
                            let bind = bind?;
                            if list_length(&bind) != Some(2) {
                                Err(anyhow!("malformed let: bind is not list of length 2"))?;
                            }
                            if let Obj::Symbol(s) = list_nth(&bind, 0).unwrap().get_obj() {
                                let value = list_nth(&bind, 1).unwrap();
                                self.emit_rec(opcodes, &value)?;
                                opcodes.push(OpCode::PushNewVar(s))
                            } else {
                                Err(anyhow!("malformed let: bind key is not symbol"))?;
                            }
                        }
                        // TODO: body have multiple expr
                        let body = list_nth(v, 2).unwrap();
                        self.emit_rec(opcodes, &body)?;
                        opcodes.push(OpCode::SetFramePrevious);
                        return Ok(());
                    },
                    _ => {},
                }
                self.emit_rec(opcodes, &cons.get_car())?;
                self.emit_cons(opcodes, &cons.get_cdr())?;
                opcodes.push(OpCode::Call);
                Ok(())
            },
            _ => Err(anyhow!("cannot emit"))?
        }
    }
}



type NativeFunc = fn(&mut Evaluator, OpaqueValue) -> Result<OpaqueValue>;

fn native_plus(evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    let pool = & evaluator.env.pool;
    let mut result = pool.get_i32(0);
    for n in list_iterator(v) {
        if let Ok(num_value) = n {
            match (result.get_obj(), num_value.get_obj()) {
                (Obj::I32(i), Obj::I32(j)) => {result = pool.get_i32(i+j)}
                _ => {return Err(anyhow!("+ error:non-number given"))}
            }
        } else {
            return Err(anyhow!("+ error: non-list given"))
        }
    }
    Ok(result)
}

pub struct Evaluator<'a> {
    current_func_id: usize,
    current_ip: usize,
    stack: Vec<OpaqueValue>,
    current_env: OpaqueValue, // envronment is list of list of pair (key(symbol), value)
    env: & 'a mut Environment,
    natives: Vec<NativeFunc>,
}

impl<'a> Evaluator<'a> {
    fn lookup(&self, s:SymbolId) -> Option<OpaqueValue> {
        for frame in list_iterator(self.current_env.clone()) {
            let frame = frame.unwrap();
            for pair in list_iterator(frame) {
                if let Obj::Cons(cons) = pair.unwrap().get_obj() {
                    if let Obj::Symbol(symbol_id) = cons.get_car().get_obj() {
                        if symbol_id == s {
                            return Some(cons.get_cdr())
                        }
                    } else {
                        panic!("internal error:unexpected environment format:car of pair is not symbol")
                    }
                } else {
                    panic!("internal error: unexpected environment format: frame is not list")
                }
            }
        }
        None
    }
    fn push_new_var(&mut self, s: SymbolId, v: OpaqueValue) -> Result<()> {
        let pool = self.env.get_pool();
        if let Obj::Cons(cons) = self.current_env.get_obj() {
            let top_frame = cons.get_car();
            let new_pair = pool.alloc_cons(pool.get_symbol_from_idx(s), v)?;
            let new_top_frame = pool.alloc_cons(new_pair, top_frame)?;
            cons.set_car(new_top_frame);
            // println!("env: {}", pool.write_to_string(&self.current_env));
            Ok(())
        } else {
            panic!("unexpected environment format: not cons")
        }
    }
    fn set_frame_previous(&mut self) {
        if let Obj::Cons(cons) = self.current_env.get_obj() {
            let prev_frame = cons.get_car();
            self.current_env = prev_frame
        } else {
            panic!("unexpected environment format: not cons")
        }
    }
    fn create_new_frame(&mut self) -> Result<()>{
        let pool = &mut self.env.pool;
        let new_frame = pool.get_nil();
        self.current_env = pool.alloc_cons(new_frame, self.current_env.clone())?;
        Ok(())
    }
    fn register_native_func(&mut self, name: &str, func: NativeFunc) -> Result<()> {
        let pool = &mut self.env.pool;
        let symbol_id = pool.get_symbol_idx(name);
        let idx = self.natives.len();
        self.natives.push(func);
        let val = pool.get_native(idx as u32);
        self.push_new_var(symbol_id, val)

    }
    fn register_native_funcs(&mut self) -> Result<()> {
        self.register_native_func("+", native_plus)?;
        self.create_new_frame()
    }
    pub fn eval(env: &mut Environment, func_id: usize) -> Result<OpaqueValue> {
        let pool = &mut env.pool;
        let initial_env = pool.alloc_cons(
            pool.get_nil(),
            pool.get_nil()
        )?;
        let mut evaluator = Evaluator {
            current_func_id: func_id,
            current_ip: 0,
            stack: Vec::new(),
            current_env: initial_env,
            env,
            natives: Vec::new(),
        };
        evaluator.register_native_funcs()?;
        loop {
            match evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip] {
                OpCode::PushI32(i) => {
                    evaluator.stack.push(evaluator.env.pool.get_i32(i))
                },
                OpCode::PushNil => {
                    evaluator.stack.push(evaluator.env.pool.get_nil())
                }
                OpCode::LookUp(s) => {
                    let value = evaluator.lookup(s).ok_or(anyhow!("undefined symbol"))?;
                    evaluator.stack.push(value)
                },
                OpCode::PushNewVar(s) => {
                    let value = evaluator.stack.pop().ok_or(anyhow!("nothing to push"))?;
                    evaluator.push_new_var(s, value)?;
                },
                OpCode::SetFramePrevious => {
                    evaluator.set_frame_previous();
                },
                OpCode::CreateNewFrame => {
                    evaluator.create_new_frame()?;
                },
                OpCode::Cons => {
                    let cdr = evaluator.stack.pop().unwrap();
                    let car = evaluator.stack.pop().unwrap();
                    let cons = evaluator.env.pool.alloc_cons(car, cdr)?;
                    evaluator.stack.push(cons);
                },
                OpCode::Call => {
                    let args = evaluator.stack.pop().unwrap();
                    let callee = evaluator.stack.pop().unwrap();
                    match callee.get_obj() {
                        Obj::Native(i) => {
                            let fun = evaluator.natives[i as usize];
                            let retval = fun(&mut evaluator, args)?;
                            evaluator.stack.push(retval)
                        }
                        _ => {return Err(anyhow!("eval error: not callable"))}
                    }
                },
                OpCode::Ret => {
                    return evaluator.stack.pop().ok_or(anyhow!("nothing to return"));
                }
            }
            evaluator.current_ip+=1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;
    use crate::parser;
    use crate::obj;

    #[test]
    fn run_small_tests() {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/small_tests.scm");
        let tests = std::fs::read_to_string(path).unwrap();
        let mut env = Environment::new();
        let v = parser::parse(&tests, env.get_pool()).unwrap();
        for result in crate::obj::list_iterator(v) {
            let v = result.unwrap();
            let expr = obj::list_nth(&v, 0).unwrap();
            // println!("evaluating {}", env.get_pool().write_to_string(&expr));
            let expected = obj::list_nth(&v, 1).unwrap();
            let func_id = env.emit(&expr).unwrap();
            let result = Evaluator::eval(&mut env, func_id).unwrap();
            assert!(
                obj::equal(&result, &expected),
                "{} evaluated to {} expected {}",
                env.get_pool().write_to_string(&expr),
                env.get_pool().write_to_string(&result),
                env.get_pool().write_to_string(&expected),
            );
        }
    }
}