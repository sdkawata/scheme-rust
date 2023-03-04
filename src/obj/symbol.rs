use std::collections::HashMap;
use std::cell::RefCell;

pub(super) type SymbolId = u32;
#[repr(C)]
#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Symbol(pub(super) SymbolId);

impl Symbol {
    pub fn as_str(&self) -> String {
        SYMBOL_POOL.with(|symbol_pool| {
           symbol_pool.borrow().symbols[self.0 as usize].to_owned()
        })
    }
}

impl std::fmt::Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

thread_local!{static SYMBOL_POOL: RefCell<SymbolPool> = RefCell::new(SymbolPool::new())}
struct SymbolPool {
    symbols: Vec<String>,
    symbols_map: HashMap<String, SymbolId>,
}

impl SymbolPool {
    fn new() -> Self {
        Self {
            symbols: Vec::new(),
            symbols_map: HashMap::new(),
        }
    }
}

pub fn from_str(s: &str) -> Symbol {
    SYMBOL_POOL.with(|symbol_pool| {
        let mut ptr = symbol_pool.borrow_mut();
        if let Some(idx) = ptr.symbols_map.get(s) {
            Symbol(*idx)
        } else {
            let idx = ptr.symbols.len() as SymbolId;
            ptr.symbols.push(s.to_owned());
            ptr.symbols_map.insert(s.to_owned(), idx);
            Symbol(idx)
        }
    })
}