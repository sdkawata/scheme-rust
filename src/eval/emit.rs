use crate::obj::{OpaqueValue, SymbolId, list_iterator, Obj, list_nth, list_length, self, FuncId};

use super::{Environment, OpCode, Func};
use anyhow::{Result, anyhow};

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

pub fn emit(env:&mut Environment, v: &OpaqueValue) -> Result<usize> {
    let opcodes = Vec::new();
    emit_func(env, opcodes, v)
}
fn emit_func(env:&mut Environment, mut opcodes: Vec<OpCode>, v: &OpaqueValue) -> Result<usize> {
    emit_rec(env, &mut opcodes, v, true)?;
    let idx = env.funcs.len();
    // eprintln!("{:?}", &opcodes);
    env.funcs.push(Func{
        opcodes
    });
    Ok(idx)
}
fn emit_cons(env: &mut Environment, opcodes: &mut Vec<OpCode>, v:&OpaqueValue) -> Result<()> {
    match v.to_owned().get_obj() {
        Obj::Cons(cons) => {
            emit_rec(env, opcodes, &cons.get_car(), false)?;
            emit_cons(env, opcodes, &cons.get_cdr())?;
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
fn emit_rec(env: &mut Environment, opcodes: &mut Vec<OpCode>, v: &OpaqueValue, tail: bool) -> Result<()> {
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
                Obj::Symbol(s) if obj::get_symbol_str(s) == "define" => {
                    let length = list_length(v).ok_or(anyhow!("malformed define: not list"))?;
                    if length < 3 {
                        Err(anyhow!("malformed define: length < 3"))?;
                    }
                    let defined = if let Obj::Symbol(s) = list_nth(v, 1).unwrap().get_obj() {
                        s
                    } else {
                        return Err(anyhow!("malformed define: not symbol"))
                    };
                    // TODO: body have multiple expr
                    let body = list_nth(v, 2).unwrap();
                    emit_rec(env, opcodes, &body, false)?;
                    opcodes.push(OpCode::AddNewVarCurrent(defined));
                    opcodes.push(OpCode::PushUndef);
                    if tail {
                        opcodes.push(OpCode::Ret);
                    }
                    return Ok(())
                },
                Obj::Symbol(s) if obj::get_symbol_str(s) == "let" => {
                    let length = list_length(v).ok_or(anyhow!("malformed let: not list"))?;
                    if length < 3 {
                        Err(anyhow!("malformed let: length < 3"))?;
                    }
                    let binds = list_nth(v, 1).unwrap();
                    opcodes.push(OpCode::PushNewFrame);
                    for bind in bind_pair_iterator(binds) {
                        let (symbol_id, expr) = bind.map_err(|e| anyhow!("malformed let:{}", e))?;
                        emit_rec(env, opcodes, &expr, false)?;
                        opcodes.push(OpCode::AddNewVar(symbol_id))
                    }
                    opcodes.push(OpCode::PopAndSetFrame);
                    // TODO: body have multiple expr
                    let body = list_nth(v, 2).unwrap();
                    emit_rec(env, opcodes, &body, tail)?;
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
                        emit_rec(env, opcodes, &expr, false)?;
                        opcodes.push(OpCode::SetVarCurrent(symbol_id));
                    }
                    // TODO: body have multiple expr
                    let body = list_nth(v, 2).unwrap();
                    emit_rec(env, opcodes, &body, tail)?;
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
                        emit_func(env, opcodes, &body)
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
                    emit_rec(env, opcodes, &cond, false)?;
                    let jmp_if_false_addr = opcodes.len();
                    opcodes.push(OpCode::Invalid);
                    emit_rec(env, opcodes, &true_branch, tail)?;
                    let jmp_addr = opcodes.len();
                    if !tail {
                        opcodes.push(OpCode::Invalid);
                    }
                    opcodes[jmp_if_false_addr] = OpCode::JmpIfFalse(opcodes.len());
                    emit_rec(env, opcodes, &false_branch, tail)?;
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
                    let idx = env.consts.len();
                    env.consts.push(quoted);
                    opcodes.push(OpCode::PushConst(idx));
                    if tail {
                        opcodes.push(OpCode::Ret)
                    }
                    return Ok(())
                },
                _ => {},
            }
            emit_rec(env, opcodes, &cons.get_car(), false)?;
            emit_cons(env, opcodes, &cons.get_cdr())?;
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