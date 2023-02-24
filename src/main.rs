mod obj;
mod parser;
mod eval;

use std::{env};
use anyhow::Result;


fn exec_file(fname: &str) -> Result<()> {
    let mut env = eval::Environment::new();
    let content = std::fs::read_to_string(fname)?;
    let obj = parser::parse(&content, env.get_pool())?;
    let func_id = env.emit(&obj)?;
    eval::Evaluator::eval(&mut env, func_id)?;
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        panic!("args.len() < 2")
    }
    exec_file(&args[1]).unwrap();
}
