use std::{
    collections::HashMap,
    io::{self, Write},
};

use anyhow::Result;

use crate::vm::Value;

pub type NativeFunction = fn(&[Value]) -> Result<Value>;

// (fn, artiy, vararg, returns value)
pub type NativeFnDesc = (NativeFunction, u8, bool, bool);

#[derive(Debug)]
pub struct NativeRegistry {
    functions: HashMap<String, NativeFnDesc>,
}

impl Default for NativeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            functions: HashMap::new(),
        };

        registry.register_io_functions();

        registry
    }

    pub fn get(&self, name: &str) -> Option<&NativeFnDesc> {
        self.functions.get(name)
    }

    pub fn register(&mut self, name: &str, func: NativeFnDesc) {
        self.functions.insert(name.to_string(), func);
    }

    fn register_io_functions(&mut self) {
        self.register("print", (native_print, 1, true, false));
    }

    pub fn has(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }
}

fn native_print(args: &[Value]) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Null);
    }

    let output: Vec<String> = args.iter().map(|a| a.format()).collect();
    print!("{}", output.join(" "));
    io::stdout().flush()?;
    Ok(Value::Null)
}
