use std::io::{Write, stdout};
use crate::obj;
use crate::obj::{OpaqueValue, Obj, SymbolId, list_iterator, list_nth, list_length, FuncId};
use anyhow::{Result, anyhow};

#[derive(Debug)]
enum OpCode {
    PushI32(i32), // stack: -> I32,
    PushTrue, // stack -> true
    PushFalse, // stack -> false
    PushUndef, // stack -> undef
    PushConst(usize), // stack -> const
    PushNil, // stack: -> nil
    LookUp(SymbolId), // stack: -> value
    AddNewVar(SymbolId), // stack: frame value -> frame
    AddNewVarCurrent(SymbolId), // stack: value ->
    SetVarCurrent(SymbolId), // stack: value ->
    PushNewFrame, // stack: -> frame
    PopAndSetFrame, // stack: frame ->
    SetFramePrevious,
    Closure(FuncId), // stack: -> closure
    TailCall, //stack: func args -> retval
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
    funcs: Vec<Func>,
    consts: Vec<OpaqueValue>,
    writer: Box<dyn Write>,
}

fn bind_pair_iterator(v: OpaqueValue) -> impl Iterator<Item=Result<(SymbolId, OpaqueValue)>> {
    list_iterator(v).map(|bind| {
        let bind = bind.map_err(|_| anyhow!("bind pair is not list"))?;
        if list_length(&bind) != Some(2) {
            Err(anyhow!("bind is not list of length 2"))?;
        }
        if let Obj::Symbol(s) = list_nth(&bind, 0).unwrap().get_obj() {
            let value = list_nth(&bind, 1).unwrap();
            Ok((s, value))
        } else {
            Err(anyhow!("bind key is not symbol"))?
        }
    })
}

impl Environment {
    pub fn new() -> Self {
        Self {
            funcs: Vec::new(),
            consts: Vec::new(),
            writer: Box::new(stdout()),
        }
    }
    pub fn emit(&mut self, v: &OpaqueValue) -> Result<usize> {
        let opcodes = Vec::new();
        self.emit_func(opcodes, v)
    }
    fn emit_func(&mut self, mut opcodes: Vec<OpCode>, v: &OpaqueValue) -> Result<usize> {
        self.emit_rec(&mut opcodes, v, true)?;
        let idx = self.funcs.len();
        // eprintln!("{:?}", &opcodes);
        self.funcs.push(Func{
            opcodes
        });
        Ok(idx)
    }
    fn emit_cons(&mut self, opcodes: &mut Vec<OpCode>, v:&OpaqueValue) -> Result<()> {
        match v.to_owned().get_obj() {
            Obj::Cons(cons) => {
                self.emit_rec(opcodes, &cons.get_car(), false)?;
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
    fn emit_rec(&mut self, opcodes: &mut Vec<OpCode>, v: &OpaqueValue, tail: bool) -> Result<()> {
        // eprintln!("emit_rec v:{} tail:{}", obj::write_to_string(v), tail);
        match v.to_owned().get_obj() {
            Obj::I32(i) => {
                opcodes.push(OpCode::PushI32(i));
                if tail {
                    opcodes.push(OpCode::Ret);
                }
                Ok(())
            },
            Obj::Symbol(s) => {
                opcodes.push(OpCode::LookUp(s));
                if tail {
                    opcodes.push(OpCode::Ret);
                }
                Ok(())
            },
            Obj::True => {
                opcodes.push(OpCode::PushTrue);
                if tail {
                    opcodes.push(OpCode::Ret);
                }
                Ok(())
            },
            Obj::False => {
                opcodes.push(OpCode::PushFalse);
                if tail {
                    opcodes.push(OpCode::Ret);
                }
                Ok(())
            },
            Obj::Cons(cons) => {
                let car = cons.get_car();
                match car.get_obj() {
                    Obj::Symbol(s) if obj::get_symbol_str(s) == "let" => {
                        let length = list_length(v).ok_or(anyhow!("malformed let: not list"))?;
                        if length < 3 {
                            Err(anyhow!("malformed let: length < 3"))?;
                        }
                        let binds = list_nth(v, 1).unwrap();
                        opcodes.push(OpCode::PushNewFrame);
                        for bind in bind_pair_iterator(binds) {
                            let (symbol_id, expr) = bind.map_err(|e| anyhow!("malformed let:{}", e))?;
                            self.emit_rec(opcodes, &expr, false)?;
                            opcodes.push(OpCode::AddNewVar(symbol_id))
                        }
                        opcodes.push(OpCode::PopAndSetFrame);
                        // TODO: body have multiple expr
                        let body = list_nth(v, 2).unwrap();
                        self.emit_rec(opcodes, &body, tail)?;
                        if !tail {
                            opcodes.push(OpCode::SetFramePrevious);
                        }
                        return Ok(());
                    },
                    Obj::Symbol(s) if obj::get_symbol_str(s) == "letrec" => {
                        let length = list_length(v).ok_or(anyhow!("malformed letrec: not list"))?;
                        if length < 3 {
                            Err(anyhow!("malformed letrec: length < 3"))?;
                        }
                        let binds = list_nth(v, 1).unwrap();
                        opcodes.push(OpCode::PushNewFrame);
                        opcodes.push(OpCode::PopAndSetFrame);
                        for bind in bind_pair_iterator(binds.clone()) {
                            let (symbol_id, _) = bind.map_err(|e| anyhow!("malformed letrec:{}", e))?;
                            opcodes.push(OpCode::PushUndef);
                            opcodes.push(OpCode::AddNewVarCurrent(symbol_id));
                        }
                        for bind in bind_pair_iterator(binds) {
                            let (symbol_id, expr) = bind.map_err(|e| anyhow!("malformed letrec:{}", e))?;
                            self.emit_rec(opcodes, &expr, false)?;
                            opcodes.push(OpCode::SetVarCurrent(symbol_id));
                        }
                        // TODO: body have multiple expr
                        let body = list_nth(v, 2).unwrap();
                        self.emit_rec(opcodes, &body, tail)?;
                        if !tail {
                            opcodes.push(OpCode::SetFramePrevious);
                        }
                        return Ok(());
                    },
                    Obj::Symbol(s) if obj::get_symbol_str(s) == "lambda" => {
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
                                    opcodes.push(OpCode::AddNewVarCurrent(s));
                                } else {
                                    return Err(anyhow!("emit error: args is not symbol"))
                                }
                            }
                            self.emit_func(opcodes, &body)
                        }?;
                        opcodes.push(OpCode::Closure(func_id as FuncId));
                        if tail {
                            opcodes.push(OpCode::Ret);
                        }
                        return Ok(())
                    },
                    Obj::Symbol(s) if obj::get_symbol_str(s) == "if" => {
                        let length = list_length(v).ok_or(anyhow!("malformed if: not list"))?;
                        if length < 4 {
                            Err(anyhow!("malformed if: length != 4"))?;
                        }
                        let cond = list_nth(v, 1).unwrap();
                        let true_branch = list_nth(v, 2).unwrap();
                        let false_branch = list_nth(v, 3).unwrap();
                        self.emit_rec(opcodes, &cond, false)?;
                        let jmp_if_false_addr = opcodes.len();
                        opcodes.push(OpCode::Invalid);
                        self.emit_rec(opcodes, &true_branch, tail)?;
                        let jmp_addr = opcodes.len();
                        if !tail {
                            opcodes.push(OpCode::Invalid);
                        }
                        opcodes[jmp_if_false_addr] = OpCode::JmpIfFalse(opcodes.len());
                        self.emit_rec(opcodes, &false_branch, tail)?;
                        if !tail {
                            opcodes[jmp_addr] = OpCode::Jmp(opcodes.len());
                        }
                        return Ok(())
                    },
                    Obj::Symbol(s) if obj::get_symbol_str(s) == "quote" => {
                        let length = list_length(v).ok_or(anyhow!("malformed letrec: not list"))?;
                        if length != 2 {
                            Err(anyhow!("malformed if: length != 2"))?;
                        }
                        let quoted = list_nth(&v, 1).unwrap();
                        let idx = self.consts.len();
                        self.consts.push(quoted);
                        opcodes.push(OpCode::PushConst(idx));
                        if tail {
                            opcodes.push(OpCode::Ret)
                        }
                        return Ok(())
                    },
                    _ => {},
                }
                self.emit_rec(opcodes, &cons.get_car(), false)?;
                self.emit_cons(opcodes, &cons.get_cdr())?;
                if tail {
                    opcodes.push(OpCode::TailCall);
                } else {
                    opcodes.push(OpCode::Call);
                }

                Ok(())
            },
            _ => Err(anyhow!("cannot emit"))?
        }
    }
}



type NativeFunc = fn(&mut Evaluator, OpaqueValue) -> Result<OpaqueValue>;

fn native_plus(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    let mut result = obj::get_i32(0);
    for n in list_iterator(v) {
        if let Ok(num_value) = n {
            match (result.get_obj(), num_value.get_obj()) {
                (Obj::I32(i), Obj::I32(j)) => {result = obj::get_i32(i+j)}
                _ => {return Err(anyhow!("+ error:non-number given"))}
            }
        } else {
            return Err(anyhow!("+ error: non-list given"))
        }
    }
    Ok(result)
}

fn native_minus(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v).ok_or_else(||anyhow!("= error: args not list"))? < 2 {
        return Err(anyhow!("= error: length < 2"))
    }
    let head = list_nth(&v, 0).unwrap();
    let mut result = match head.clone().get_obj() {
        Obj::I32(_) => head,
        _ => {return Err(anyhow!("- error: not number"))}
    };
    for tail in list_iterator(v).skip(1) {
        match (result.get_obj(), tail.unwrap().get_obj()) {
            (Obj::I32(i), Obj::I32(j)) => {
                result = obj::get_i32(i-j);
            }
            _ => {return Err(anyhow!("= error:cannot compare"))}
        }
    }
    Ok(result)
}

fn native_eq(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v).ok_or_else(|| anyhow!("= error: args not list"))? < 2 {
        return Err(anyhow!("= error: length < 2"))
    }
    let head_obj = list_nth(&v, 0).unwrap().get_obj();
    for tail in list_iterator(v).skip(1) {
        match (head_obj.clone(), tail.unwrap().get_obj()) {
            (Obj::I32(i), Obj::I32(j)) => {
                if i != j {
                    return Ok(obj::get_false())
                }
            }
            _ => {return Err(anyhow!("= error:cannot compare"))}
        }
    }
    Ok(obj::get_true())
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

fn native_cons(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(2) {
        return Err(anyhow!("cons error: args length != 2"))
    }
    let car = list_nth(&v, 0).unwrap();
    let cdr = list_nth(&v, 1).unwrap();
    Ok(obj::alloc_cons(car, cdr)?)
}

fn native_null_p(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("null? error: args length != 1"))
    }
    if let Obj::Nil = list_nth(&v, 0).unwrap().get_obj() {
        Ok(obj::get_true())
    } else {
        Ok(obj::get_false())
    }
}

fn native_write(evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("write error: args length != 1"))
    }
    let v = list_nth(&v, 0).unwrap();
    obj::write(&mut evaluator.env.writer, &v)?;
    Ok(obj::get_undef())
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
        obj::frame::lookup(s, &self.current_env)
    }
    fn add_new_var(&mut self, frame: OpaqueValue, s: SymbolId, v: OpaqueValue) -> Result<()> {
        obj::frame::add_new_var(frame,s,v)
    }
    fn set_var(&mut self, frame: OpaqueValue, s: SymbolId, v: OpaqueValue) -> Result<()> {
        obj::frame::set_var(frame,s,v)
    }
    fn set_frame_previous(&mut self) -> Result<()> {
        self.current_env = obj::frame::previous_frame(self.current_env.clone())?;
        Ok(())
    }
    fn set_new_frame(&mut self) -> Result<()> {
        self.current_env = obj::frame::extend_frame(&self.current_env)?;
        Ok(())
    }
    fn create_new_frame(&mut self) -> Result<OpaqueValue>{
        obj::frame::extend_frame(&self.current_env)
    }
    fn register_native_func(&mut self, name: &str, func: NativeFunc) -> Result<()> {
        let symbol_id = obj::get_symbol_idx(name);
        let idx = self.natives.len();
        self.natives.push(func);
        let val = obj::get_native(idx as u32);
        self.add_new_var(self.current_env.clone(), symbol_id, val)
    }
    fn register_native_funcs(&mut self) -> Result<()> {
        self.register_native_func("+", native_plus)?;
        self.register_native_func("-", native_minus)?;
        self.register_native_func("=", native_eq)?;
        self.register_native_func("car", native_car)?;
        self.register_native_func("cdr", native_cdr)?;
        self.register_native_func("cons", native_cons)?;
        self.register_native_func("null?", native_null_p)?;
        self.register_native_func("write", native_write)?;
        self.set_new_frame()
    }
    fn push_stack(&mut self, v: OpaqueValue) {
        self.stack.push(v)
    }
    fn peek_stack(&mut self) -> Result<OpaqueValue> {
        Ok(self.stack.last().ok_or_else(|| anyhow!("eval error:trying to peek from empty stack"))?.clone())
    }
    fn pop_stack(&mut self) -> Result<OpaqueValue> {
        self.stack.pop().ok_or_else(|| anyhow!("eval error:trying to pop from empty stack"))
    }
    fn shrink_stack(&mut self, target_len:usize) {
        if target_len > self.stack.len() {
            panic!("shrink to bigger size");
        }
        while target_len < self.stack.len() {
            self.pop_stack().unwrap();
        }
    }
    fn proc_ret(&mut self, stack_top: CallStack, retval: OpaqueValue) -> Result<()> {
        self.current_func_id = stack_top.ret_func_id;
        self.current_ip = stack_top.ret_ip;
        self.shrink_stack(stack_top.ret_base_pointer);
        self.current_env = self.pop_stack()?;
        self.push_stack(retval);
        Ok(())
    }
    pub fn eval(env: &mut Environment, func_id: usize) -> Result<OpaqueValue> {
        let initial_env = obj::alloc_cons(
            obj::get_nil(),
            obj::get_nil()
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
            // eprintln!("current_env: {}", obj::write_to_string(&evaluator.current_env.get_value()));
            // eprintln!("stack top: {}", evaluator.peek_stack().map(|v| obj::write_to_string(&v)).or_else(|_| Ok::<String, anyhow::Error>("no stack".to_string()))?);
            match evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip] {
                OpCode::PushI32(i) => {
                    evaluator.push_stack(obj::get_i32(i))
                },
                OpCode::PushConst(const_idx) => {
                    evaluator.push_stack(evaluator.env.consts[const_idx].clone());
                }
                OpCode::PushNil => {
                    evaluator.push_stack(obj::get_nil())
                },
                OpCode::PushTrue => {
                    evaluator.push_stack(obj::get_true())
                },
                OpCode::PushFalse => {
                    evaluator.push_stack(obj::get_false())
                },
                OpCode::PushUndef => {
                    evaluator.push_stack(obj::get_undef())
                },
                OpCode::LookUp(s) => {
                    // eprintln!("{}", obj::write_to_string(&evaluator.current_env));
                    let value = evaluator.lookup(s).ok_or_else(|| anyhow!("undefined symbol: {}", obj::get_symbol_str(s)))?;
                    evaluator.push_stack(value)
                },
                OpCode::AddNewVar(s) => {
                    let value = evaluator.pop_stack()?;
                    let frame = evaluator.peek_stack()?;
                    evaluator.add_new_var(frame, s, value)?;
                },
                OpCode::AddNewVarCurrent(s) => {
                    let value = evaluator.pop_stack()?;
                    evaluator.add_new_var(evaluator.current_env.clone(), s, value)?;
                },
                OpCode::SetVarCurrent(s) => {
                    let value = evaluator.pop_stack()?;
                    evaluator.set_var(evaluator.current_env.clone(), s, value)?;
                },
                OpCode::PopAndSetFrame => {
                    let frame = evaluator.pop_stack()?;
                    evaluator.current_env = frame;
                }
                OpCode::SetFramePrevious => {
                    evaluator.set_frame_previous()?;
                },
                OpCode::PushNewFrame => {
                    let new_frame = evaluator.create_new_frame()?;
                    evaluator.push_stack(new_frame);
                },
                OpCode::Cons => {
                    let cdr = evaluator.pop_stack()?;
                    let car = evaluator.pop_stack()?;
                    let cons = obj::alloc_cons(car, cdr)?;
                    evaluator.push_stack(cons);
                },
                OpCode::CarCdr => {
                    let cons = evaluator.pop_stack().unwrap();
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
                    match callee.clone().get_obj() {
                        Obj::Native(i) => {
                            let fun = evaluator.natives[i as usize];
                            let retval = fun(&mut evaluator, args)?;
                            evaluator.push_stack(retval)
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
                            evaluator.set_new_frame()?;
                            continue;
                        },
                        _ => {return Err(anyhow!("eval error: not callable {:?}", obj::write_to_string(&callee)))}
                    }
                },
                OpCode::TailCall => {
                    let args = evaluator.pop_stack().unwrap();
                    let callee = evaluator.pop_stack().unwrap();
                    match callee.clone().get_obj() {
                        Obj::Native(i) => {
                            let fun = evaluator.natives[i as usize];
                            let retval = fun(&mut evaluator, args)?;
                            if let Some(call_stack) = evaluator.call_stack.pop() {
                                evaluator.proc_ret(call_stack, retval)?;
                                continue;
                            } else {
                                return Ok(retval);
                            }
                        },
                        Obj::Closure(closure) => {
                            let func_id = closure.get_func_id();
                            let env = closure.get_env();
                            evaluator.push_stack(args);
                            evaluator.current_func_id = func_id as usize;
                            evaluator.current_ip = 0;
                            evaluator.current_env = env;
                            evaluator.set_new_frame()?;
                            continue;
                        },
                        _ => {return Err(anyhow!("eval error: not callable {:?}", obj::write_to_string(&callee)))}
                    }
                }
                OpCode::Closure(func_id) => {
                    let closure = obj::alloc_closure(func_id as FuncId, evaluator.current_env.clone())?;
                    evaluator.push_stack(closure)
                },
                OpCode::Ret => {
                    let retval = evaluator.pop_stack()?;
                    if let Some(call_stack) = evaluator.call_stack.pop() {
                        evaluator.proc_ret(call_stack, retval)?;
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

    fn assert_evaluated_to(env: &mut Environment, expr: &OpaqueValue, expected: &OpaqueValue) -> Result<()> {
        let func_id = env.emit(&expr).unwrap();
        let result = Evaluator::eval(env, func_id)?;
        assert!(
            obj::equal(&result, &expected),
            "{} evaluated to {} expected {}",
            obj::write_to_string(&expr),
            obj::write_to_string(&result),
            obj::write_to_string(&expected),
        );
        Ok(())
    }

    #[test]
    fn run_small_tests() {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/small_tests.scm");
        let tests = std::fs::read_to_string(path).unwrap();
        let mut env = Environment::new();
        let parsed = parser::parse(&tests,).unwrap();
        obj::set_force_gc_every_alloc(true);
        for pair in list_iterator(parsed) {
            let pair = pair.unwrap();
            let expr = obj::list_nth(&pair, 0).unwrap();
            // eprintln!("evaluating {}", obj::write_to_string(&expr.get_value()));
            let expected = obj::list_nth(&pair, 1).unwrap();
            assert_evaluated_to(&mut env, &expr, &expected).map_err(|err|
                anyhow!("error evaluating {}:{}", obj::write_to_string(&expr), err)
            ).unwrap();
        }
        obj::set_force_gc_every_alloc(false);
    }
}