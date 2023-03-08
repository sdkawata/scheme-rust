use std::io::{Write, stdout};
use crate::obj;
use crate::obj::list::ElemOrTail;
use crate::obj::{OpaqueValue, Obj, list::list_iterator, list::list_nth, list::list_length, FuncId};
use obj::symbol::Symbol;
use anyhow::{Result, anyhow};

mod emit;
pub use emit::emit;

#[derive(Debug)]
enum OpCode {
    PushI32(i32), // stack: -> I32,
    PushF32(f32), // stack: -> f32,
    PushChar(char), // stack: -> char,
    PushTrue, // stack -> true
    PushFalse, // stack -> false
    PushUndef, // stack -> undef
    PushConst(usize), // stack -> const
    PushNil, // stack: -> nil
    LookUp(Symbol), // stack: -> value
    AddNewVar(Symbol), // stack: frame value -> frame
    AddNewVarCurrent(Symbol), // stack: value ->
    SetVarCurrent(Symbol), // stack: value ->
    PushNewFrame, // stack: -> frame
    PopAndSetFrame, // stack: frame ->
    SetFramePrevious,
    Closure(FuncId), // stack: -> closure
    TailCall, //stack: func args -> retval
    Call, // stack: func args -> retval
    CarCdr, // stack: cons -> car cdr
    Cons, // stack: car cdr -> cons
    Ret, // stack: Retval ->
    JmpIfTruePreserve(usize), // stack: val -> val
    JmpIfFalsePreserve(usize), // stack: val -> val
    JmpIfFalse(usize), // stack: val ->
    Jmp(usize), // stack: ->
    Discard, // stack: value ->
    Invalid,
}

struct Func {
    opcodes: Vec<OpCode>,
}

pub struct Environment {
    funcs: Vec<Func>,
    consts: Vec<OpaqueValue>,
    pub writer: Box<dyn Write>,
    top_level_env: OpaqueValue,
    natives: Vec<NativeFunc>,
}

impl Environment {
    fn register_native_func(&mut self, name: &str, func: NativeFunc) -> Result<()> {
        let symbol = obj::symbol::from_str(name);
        let idx = self.natives.len();
        self.natives.push(func);
        let val = obj::get_native(idx as u32);
        obj::frame::add_new_var(self.top_level_env.clone(), symbol, val)
    }
    fn register_native_funcs(&mut self) -> Result<()> {
        self.register_native_func("+", native_plus)?;
        self.register_native_func("*", native_times)?;
        self.register_native_func("-", native_minus)?;
        self.register_native_func("/", native_div)?;
        self.register_native_func(">", native_gt)?;
        self.register_native_func("=", native_eq)?;
        self.register_native_func("car", native_car)?;
        self.register_native_func("cdr", native_cdr)?;
        self.register_native_func("cons", native_cons)?;
        self.register_native_func("null?", native_null_p)?;
        self.register_native_func("write", native_write)?;
        self.register_native_func("display", native_display)?;
        self.register_native_func("write", native_write)?;
        Ok(())
    }
    pub fn new() -> Self {
        let mut new_env = Self {
            funcs: Vec::new(),
            consts: Vec::new(),
            writer: Box::new(stdout()),
            top_level_env: obj::frame::empty_frame().unwrap(),
            natives: Vec::new(),
        };
        new_env.register_native_funcs().unwrap();
        new_env
    }
}

type NativeFunc = fn(&mut Evaluator, OpaqueValue) -> Result<OpaqueValue>;

fn must_as_i32(v:OpaqueValue) -> i32 {
    match v.get_obj() {
        Obj::I32(i) => i,
        _ => unreachable!(),
    }
}

fn must_as_f32(v:OpaqueValue) -> f32 {
    match v.get_obj() {
        Obj::I32(i) => i as f32,
        Obj::F32(f) => f,
        _ => unreachable!(),
    }
}

fn is_numeric(v:&OpaqueValue) ->bool {
    v.is_f32() || v.is_i32()
}

#[inline]
fn numeric_binary_operator<F:Fn(i32,i32)->i32, F2:Fn(f32,f32) -> f32>
    (v: OpaqueValue, initial: Option<OpaqueValue>, name: &str, f_i32: F, f_f32:F2) -> Result<OpaqueValue> {
    let mut iter = list_iterator(v);
    let mut result = match initial {
        Some(v) => v,
        None => match iter.next() {
            Some(ElemOrTail::Elem(v)) if (is_numeric(&v)) => v,
            Some(ElemOrTail::Elem(_)) => {return Err(anyhow!("{} error: arg type not numeric", name));}
            Some(_) => {return Err(anyhow!("{} error: arg is not list", name));}
            None => {return Err(anyhow!("{} error: arg len < 1", name));}
        }
    };
    for n in iter  {
        if let ElemOrTail::Elem(v) = n {
            if !is_numeric(&v) {
                return Err(anyhow!("{} error: arg type not numeric", name));
            }
            if result.is_i32() && v.is_i32() {
                result = obj::get_i32(f_i32(must_as_i32(result), must_as_i32(v)))
            } else {
                result = obj::get_f32(f_f32(must_as_f32(result), must_as_f32(v)))
            }
        } else {
            return Err(anyhow!("{} error: arg len < 1", name));
        }
    }
    Ok(result)
}

fn native_plus(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    numeric_binary_operator(v, Some(obj::get_i32(0)), "+", |i,j|{i+j}, |i,j|{i+j})
}

fn native_times(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    numeric_binary_operator(v, Some(obj::get_i32(1)), "*", |i,j|{i*j}, |i,j|{i*j})
}

fn native_minus(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    numeric_binary_operator(v, None, "-", |i,j|{i-j}, |i,j|{i-j})
}

fn native_div(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    numeric_binary_operator(v, None, "/", |i,j|{i/j}, |i,j|{i/j})
}

fn native_gt(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    let mut iter = list_iterator(v);
    let mut previous = if let Some(ElemOrTail::Elem(v)) = iter.next() {
        v
    } else {
        return Err(anyhow!("> error: arg len < 2"))
    };
    if !previous.is_f32() && !previous.is_i32() {
        return Err(anyhow!("> error: not numeric"))
    }
    for v in iter {
        if let ElemOrTail::Elem(v) = v {
            if ! is_numeric(&v) {
                return Err(anyhow!("> error: non-numeric value given"))
            }
            if previous.is_i32() && v.is_i32() {
                if must_as_i32(previous.clone()) <= must_as_i32(v.clone()) {
                    return Ok(obj::get_false())
                }
            } else {
                if must_as_f32(previous.clone()) <= must_as_f32(v.clone()) {
                    return Ok(obj::get_false())
                }
            }
        } else {
            return Err(anyhow!("> error: not list"))
        }
    }
    Ok(obj::get_true())
}

fn native_eq(_evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v).ok_or_else(|| anyhow!("= error: args not list"))? < 2 {
        return Err(anyhow!("= error: length < 2"))
    }
    let head_obj = list_nth(&v, 0).unwrap().get_obj();
    for tail in list_iterator(v).skip(1) {
        match (head_obj.clone(), tail.expect_elem().unwrap().get_obj()) {
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
fn native_display(evaluator: &mut Evaluator, v: OpaqueValue) -> Result<OpaqueValue> {
    if list_length(&v) != Some(1) {
        return Err(anyhow!("write error: args length != 1"))
    }
    let v = list_nth(&v, 0).unwrap();
    obj::display(&mut evaluator.env.writer, &v)?;
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
    call_stack: Vec<CallStack>,
}

impl<'a> Evaluator<'a> {
    fn lookup(&self, s:Symbol) -> Option<OpaqueValue> {
        obj::frame::lookup(s, &self.current_env)
    }
    fn add_new_var(&mut self, frame: OpaqueValue, s: Symbol, v: OpaqueValue) -> Result<()> {
        obj::frame::add_new_var(frame,s,v)
    }
    fn set_var(&mut self, frame: OpaqueValue, s: Symbol, v: OpaqueValue) -> Result<()> {
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
        let mut evaluator = Evaluator {
            current_func_id: func_id,
            current_ip: 0,
            stack: Vec::new(),
            current_env: env.top_level_env.clone(),
            call_stack: Vec::new(),
            env,
        };
        loop {
            // eprintln!("func_id: {} ip:{} opcode:{:?}", evaluator.current_func_id, evaluator.current_ip, evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip]);
            // eprintln!("current_env: {}", obj::write_to_string(&evaluator.current_env.get_value()));
            // eprintln!("stack top: {}", evaluator.peek_stack().map(|v| obj::write_to_string(&v)).or_else(|_| Ok::<String, anyhow::Error>("no stack".to_string()))?);
            match evaluator.env.funcs[evaluator.current_func_id].opcodes[evaluator.current_ip] {
                OpCode::PushI32(i) => {
                    evaluator.push_stack(obj::get_i32(i))
                },
                OpCode::PushF32(f) => {
                    evaluator.push_stack(obj::get_f32(f))
                },
                OpCode::PushChar(c) => {
                    evaluator.push_stack(obj::get_char(c))
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
                    let value = evaluator.lookup(s).ok_or_else(|| anyhow!("undefined symbol: {}", s.as_str()))?;
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
                            let fun = evaluator.env.natives[i as usize];
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
                            let fun = evaluator.env.natives[i as usize];
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
                OpCode::JmpIfTruePreserve(addr) => {
                    let cond = evaluator.peek_stack()?;
                    if let Obj::False = cond.get_obj() {
                    } else {
                        evaluator.current_ip = addr;
                        continue;
                    }
                },
                OpCode::JmpIfFalsePreserve(addr) => {
                    let cond = evaluator.peek_stack()?;
                    if let Obj::False = cond.get_obj() {
                        evaluator.current_ip = addr;
                        continue;
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
                OpCode::Discard => {
                    evaluator.pop_stack()?;
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
        let func_id = emit(env, &expr).unwrap();
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
            let pair = pair.expect_elem().unwrap();
            let expr = obj::list::list_nth(&pair, 0).unwrap();
            // eprintln!("evaluating {}", obj::write_to_string(&expr.get_value()));
            let expected = obj::list::list_nth(&pair, 1).unwrap();
            assert_evaluated_to(&mut env, &expr, &expected).map_err(|err|
                anyhow!("error evaluating {}:{}", obj::write_to_string(&expr), err)
            ).unwrap();
        }
        obj::set_force_gc_every_alloc(false);
    }
}