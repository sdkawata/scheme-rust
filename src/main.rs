mod obj;
mod parser;
mod eval;

use std::{env};
use anyhow::Result;


fn exec_file(fname: &str) -> Result<()> {
    let mut env = eval::Environment::new();
    let content = std::fs::read_to_string(fname)?;
    let obj = parser::parse(&content)?;
    let func_id = env.emit(&obj)?;
    eval::Evaluator::eval(&mut env, func_id)?;
    Ok(())
}

fn main() {
    #[cfg(feature = "profile")]
    let guard = pprof::ProfilerGuardBuilder::default().frequency(100000).blocklist(&["libc", "libgcc", "pthread", "vdso"]).build().unwrap();
    
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        panic!("args.len() < 2")
    }
    exec_file(&args[1]).unwrap();

    #[cfg(feature = "profile")]
    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();
    };
}
