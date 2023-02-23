use crate::obj::{ObjPool, OpaqueValue, Obj, SymbolId, list_iterator, list_nth, list_length, FuncId};
use anyhow::{Result, anyhow};

#[derive(Debug)]
enum OpCode {
    PushI32(i32), // stack: -> I32,
    PushTrue, // stack -> true
    PushFalse, // stack -> false
    PushUndef, // stack -> undef
    PushConst(usize), // stack -> const
    PushNil, // stack: -> nil
    LookUp(SymbolId), // stack: -> Value
    PushNewVar(SymbolId), // stack: Value ->
    CreateNewFrame, 
    SetFramePrevious,
    Closure(FuncId), // stack: -> closure
    Call, // stack: func args -> retval
    CarCdr, // stack: cons -> car cdr
    Cons, // stack: car cdr -> cons
    Ret, // stack: Retval ->
    JmpIfFalse(usize), // stack: val ->
    Jmp(usize), // stack: ->
    Invalid,
}

struct Func {
    opcodes: Vec<OpCode>,
}

pub struct Environment {
    pool: ObjPool,
    funcs: Vec<Func>,
    consts: Vec<OpaqueValue>,
}

impl Environment {
    pub fn new() -> Self {
        Self {
            pool: ObjPool::new(1000000),
            funcs: Vec::new(),
            consts: Vec::new(),
        }
    }
    pub fn get_pool(&mut self) -> &mut ObjPool {
        &mut self.pool
    }
    pub fn emit(&mut self, v: &OpaqueValue) -> Result<usize> {
        let opcodes = Vec::new();
        self.emit_func(opcodes, v)
    }
    fn emit_func(&mut self, mut opcodes: Vec<OpCode>, v: &OpaqueValue) -> Result<usize> {
        self.emit_rec(&mut opcodes, v)?;
        opcodes.push(OpCode::Ret);
        let idx = self.funcs.len();
        // eprintln!("{:?}", &opcodes);
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
            Obj::True => {
                opcodes.push(OpCode::PushTrue);
                Ok(())
            },
            Obj::False => {
                opcodes.push(OpCode::PushFalse);
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
                    Obj::Symbol(s) if self.pool.get_symbol_str(s) == "lambda" => {
                        let length = list_length(v).ok_or(anyhow!("malformed lambda: not list"))?;
                        if length != 3 {
                            Err(anyhow!("malformed lambda: length != 3"))?;
                        }
                        let args = list_nth(v, 1).unwrap();
                        let body = list_nth(v, 2).unwrap();
                        if list_length(&args) == None {
                            return Err(anyhow!("emit error: args is not list"))
                        }
                        let func_id = {
                            let mut opcodes = Vec::<OpCode>::new();
                            for v in list_iterator(args) {
                                if let Obj::Symbol(s) = v.unwrap().get_obj() {
                                    opcodes.push(OpCode::CarCdr);
                                    opcodes.push(OpCode::PushNewVar(s));
                                } else {
                                    return Err(anyhow!("emit error: args is not symbol"))
                                }
                            }
                            self.emit_func(opcodes, &body)
                        }?;
                        opcodes.push(OpCode::Closure(func_id as FuncId));
                        return Ok(())
                    },
                    Obj::Symbol(s) if self.pool.get_symbol_str(s) == "if" => {
                        let length = list_length(v).ok_or(anyhow!("malformed if: not list"))?;
                        if length < 4 {
                            Err(anyhow!("malformed if: length != 4"))?;
                        }
                        let cond = list_nth(v, 1).unwrap();
                        let true_branch = list_nth(v, 2).unwrap();
                        let false_branch = list_nth(v, 3).unwrap();
                        self.emit_rec(opcodes, &cond)?;
                        let jmp_if_false_addr = opcodes.len();
                        opcodes.push(OpCode::Invalid);
                        self.emit_rec(opcodes, &true_branch)?;
                        let jmp_addr = opcodes.len();
                        opcodes.push(OpCode::Invalid);
                        opcodes[jmp_if_false_addr] = OpCode::JmpIfFalse(opcodes.len());
                        self.emit_rec(opcodes, &false_branch)?;
                        opcodes[jmp_addr] = OpCode::Jmp(opcodes.len());
                        return Ok(())
                    },
                    Obj::Symbol(s) if self.pool.get_symbol_str(s) == "quote" => {
                        let length = list_length(v).ok_or(anyhow!("malformed letrec: not list"))?;
                        if length != 2 {
                            Err(anyhow!("malformed if: length != 2"))?;
                        }
                        let quoted = list_nth(&v, 1).unwrap();
                        let idx = self.consts.len();
                        self.consts.push(quoted);
                        opcodes.push(OpCode::PushConst(idx));
                        return Ok(())
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

fn native_eq(evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v).ok_or(anyhow!("= error: args not list"))? < 2 {
        return Err(anyhow!("= error: length < 2"))
    }
    let head = list_nth(&v, 0).unwrap();
    for tail in list_iterator(v).skip(1) {
        match (head.get_obj(), tail.unwrap().get_obj()) {
            (Obj::I32(i), Obj::I32(j)) => {
                if i != j {
                    return Ok(evaluator.env.pool.get_false())
                }
            }
            _ => {return Err(anyhow!("= error:cannot compare"))}
        }
    }
    Ok(evaluator.env.pool.get_true())
}

fn native_car(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("car error: args length != 1"))
    }
    if let Obj::Cons(cons) = list_nth(&v, 0).unwrap().get_obj() {
        Ok(cons.get_car())
    } else {
        Err(anyhow!("car error: non-list given"))
    }
}

fn native_cdr(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("cdr error: args length != 1"))
    }
    if let Obj::Cons(cons) = list_nth(&v, 0).unwrap().get_obj() {
        Ok(cons.get_cdr())
    } else {
        Err(anyhow!("car error: non-list given"))
    }
}

fn native_null_p(evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("null? error: args length != 1"))
    }
    if let Obj::Nil = list_nth(&v, 0).unwrap().get_obj() {
        Ok(evaluator.env.pool.get_true())
    } else {
        Ok(evaluator.env.pool.get_false())
    }
}

struct CallStack {
    ret_func_id: usize,
    ret_ip: usize,
    ret_base_pointer: usize,
}

pub struct Evaluator<'a> {
    current_func_id: usize,
    current_ip: usize,
    stack: Vec<OpaqueValue>,
    current_env: OpaqueValue, // envronment is list of list of pair (key(symbol), value)
    env: & 'a mut Environment,
    natives: Vec<NativeFunc>,
    call_stack: Vec<CallStack>,
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
        self.register_native_func("=", native_eq)?;
        self.register_native_func("car", native_car)?;
        self.register_native_func("cdr", native_cdr)?;
        self.register_native_func("null?", native_null_p)?;
        self.create_new_frame()
    }
    fn push_stack(&mut self, v: OpaqueValue) {
        self.stack.push(v)
    }
    fn pop_stack(&mut self) -> Result<OpaqueValue> {
        self.stack.pop().ok_or(anyhow!("eval error:trying to pop from empty stack"))
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
            call_stack: Vec::new(),
        };
        evaluator.register_native_funcs()?;
        loop {
            // eprintln!("func_id: {} ip:{} opcode:{:?}", evaluator.current_func_id, evaluator.current_ip, evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip]);
            match evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip] {
                OpCode::PushI32(i) => {
                    evaluator.push_stack(evaluator.env.pool.get_i32(i))
                },
                OpCode::PushConst(const_idx) => {
                    evaluator.push_stack(evaluator.env.consts[const_idx].clone());
                }
                OpCode::PushNil => {
                    evaluator.push_stack(evaluator.env.pool.get_nil())
                },
                OpCode::PushTrue => {
                    evaluator.push_stack(evaluator.env.pool.get_true())
                },
                OpCode::PushFalse => {
                    evaluator.push_stack(evaluator.env.pool.get_false())
                },
                OpCode::PushUndef => {
                    evaluator.push_stack(evaluator.env.pool.get_undef())
                },
                OpCode::LookUp(s) => {
                    // eprintln!("{}", evaluator.env.pool.write_to_string(&evaluator.current_env));
                    let value = evaluator.lookup(s).ok_or(anyhow!("undefined symbol: {}", evaluator.env.pool.get_symbol_str(s)))?;
                    evaluator.push_stack(value)
                },
                OpCode::PushNewVar(s) => {
                    let value = evaluator.pop_stack()?;
                    evaluator.push_new_var(s, value)?;
                },
                OpCode::SetFramePrevious => {
                    evaluator.set_frame_previous();
                },
                OpCode::CreateNewFrame => {
                    evaluator.create_new_frame()?;
                },
                OpCode::Cons => {
                    let cdr = evaluator.pop_stack()?;
                    let car = evaluator.pop_stack()?;
                    let cons = evaluator.env.pool.alloc_cons(car, cdr)?;
                    evaluator.stack.push(cons);
                },
                OpCode::CarCdr => {
                    let cons = evaluator.stack.pop().unwrap();
                    if let Obj::Cons(cons) = cons.get_obj() {
                        evaluator.push_stack(cons.get_cdr());
                        evaluator.push_stack(cons.get_car());
                    } else {
                        return Err(anyhow!("eval error: carcdr inst encounter non-cons"))
                    }
                }
                OpCode::Call => {
                    let args = evaluator.pop_stack().unwrap();
                    let callee = evaluator.pop_stack().unwrap();
                    match callee.get_obj() {
                        Obj::Native(i) => {
                            let fun = evaluator.natives[i as usize];
                            let retval = fun(&mut evaluator, args)?;
                            evaluator.stack.push(retval)
                        },
                        Obj::Closure(closure) => {
                            let func_id = closure.get_func_id();
                            let env = closure.get_env();
                            evaluator.push_stack(evaluator.current_env.clone());
                            evaluator.call_stack.push(
                                CallStack { 
                                    ret_func_id: evaluator.current_func_id,
                                    ret_ip: evaluator.current_ip + 1,
                                    ret_base_pointer: evaluator.stack.len()
                                }
                            );
                            evaluator.push_stack(args);
                            evaluator.current_func_id = func_id as usize;
                            evaluator.current_ip = 0;
                            evaluator.current_env = env;
                            continue;
                        },
                        _ => {return Err(anyhow!("eval error: not callable {:?}", evaluator.env.pool.write_to_string(&callee)))}
                    }
                },
                OpCode::Closure(func_id) => {
                    let closure = evaluator.env.pool.alloc_closure(func_id as FuncId, evaluator.current_env.clone())?;
                    evaluator.push_stack(closure)
                },
                OpCode::Ret => {
                    let retval = evaluator.pop_stack()?;
                    if let Some(call_stack) = evaluator.call_stack.pop() {
                        evaluator.current_func_id = call_stack.ret_func_id;
                        evaluator.current_ip = call_stack.ret_ip;
                        evaluator.stack.resize(call_stack.ret_base_pointer, evaluator.env.pool.get_nil());
                        evaluator.current_env = evaluator.pop_stack()?;
                        evaluator.push_stack(retval);
                        continue;
                    } else {
                        // no call stack return from eval loop
                        return Ok(retval);
                    }

                },
                OpCode::JmpIfFalse(addr) => {
                    let cond = evaluator.pop_stack()?;
                    if let Obj::False = cond.get_obj() {
                        evaluator.current_ip = addr;
                        continue;
                    }
                },
                OpCode::Jmp(addr) => {
                    evaluator.current_ip = addr;
                    continue;
                },
                OpCode::Invalid => {
                    return Err(anyhow!("internal error: encounter invalid opcode"))
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
    use anyhow::Result;

    fn assert_evaluated_to(env: &mut Environment, expr: OpaqueValue, expected: OpaqueValue) -> Result<()> {
        let func_id = env.emit(&expr).unwrap();
        let result = Evaluator::eval(env, func_id)?;
        assert!(
            obj::equal(&result, &expected),
            "{} evaluated to {} expected {}",
            env.get_pool().write_to_string(&expr),
            env.get_pool().write_to_string(&result),
            env.get_pool().write_to_string(&expected),
        );
        Ok(())
    }

    #[test]
    fn run_small_tests() {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/small_tests.scm");
        let tests = std::fs::read_to_string(path).unwrap();
        let mut env = Environment::new();
        let v = parser::parse(&tests, env.get_pool()).unwrap();
        for result in crate::obj::list_iterator(v) {
            let pair = result.unwrap();
            let expr = obj::list_nth(&pair, 0).unwrap();
            // println!("evaluating {}", env.get_pool().write_to_string(&expr));
            let expected = obj::list_nth(&pair, 1).unwrap();
            assert_evaluated_to(&mut env, expr.clone(), expected.clone()).map_err(|err|
                anyhow!("error evaluating {}:{}", env.pool.write_to_string(&expr), err)
            ).unwrap();
        }
    }
}