mod obj;
mod parser;
mod eval;

use std::{env};
use anyhow::Result;


fn exec_file(fname: &str, env: &mut eval::Environment) -> Result<()> {
    let content = std::fs::read_to_string(fname)?;
    let obj = parser::parse(&content)?;
    let func_id = env.emit(&obj)?;
    eval::Evaluator::eval(env, func_id)?;
    Ok(())
}

fn main() {
    #[cfg(feature = "profile")]
    let guard = pprof::ProfilerGuardBuilder::default().frequency(100000).blocklist(&["libc", "libgcc", "pthread", "vdso"]).build().unwrap();
    
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        panic!("args.len() < 2")
    }
    let mut env = eval::Environment::new();
    exec_file(&args[1], &mut env).unwrap();

    #[cfg(feature = "profile")]
    if let Ok(report) = guard.report().build() {
        let file = std::fs::File::create("flamegraph.svg").unwrap();
        report.flamegraph(file).unwrap();
    };
}

#[cfg(test)]
mod test {
    use std::path::PathBuf;
    use super::*;

    mod pipe {
        use std::cell::RefCell;
        use std::rc::Rc;
        use std::io::Write;

        pub struct Writer {
            vec: Rc<RefCell<Vec<u8>>>
        }
        impl Write for Writer {
            fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
                self.vec.borrow_mut().extend(buf);
                Ok(buf.len())
            }
            fn flush(&mut self) -> std::io::Result<()> {
                Ok(())
            }
        }
        pub struct Reader {
            vec: Rc<RefCell<Vec<u8>>>
        }
        impl Reader {
            pub fn get_string(&self) -> anyhow::Result<String> {
                Ok(String::from_utf8(self.vec.borrow().to_owned())?)
            }
        }

        pub fn create_pair() -> (Writer, Reader) {
            let vec = Rc::new(RefCell::new(Vec::<u8>::new()));
            (Writer{vec:vec.clone()}, Reader{vec:vec.clone()})
        }
    }

    #[test]
    fn test_runs() {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/runs");
        for file in std::fs::read_dir(path).unwrap() {
            let dir_entry = file.unwrap();
            if dir_entry.file_name().to_str().unwrap().ends_with(".scm") {
                let mut env = eval::Environment::new();
                let (writer, reader) = pipe::create_pair();
                env.writer = Box::new(writer);
                exec_file(&dir_entry.path().to_str().unwrap(), &mut env).unwrap();
                let output = reader.get_string().unwrap();
                let expected_path = format!("{}.out", dir_entry.path().display());
                let expected = std::fs::read_to_string(expected_path).unwrap();
                assert_eq!(expected, output);
            }
        }
    }
}