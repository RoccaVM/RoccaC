use std::{
    collections::HashMap,
    io::{self, Write},
};

use anyhow::Result;

use crate::vm::Value;

pub type NativeFunction = fn(&[Value]) -> Result<Value>;

#[derive(Debug)]
pub struct NativeRegistry {
    functions: HashMap<String, NativeFunction>,
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

    pub fn get(&self, name: &str) -> Option<&NativeFunction> {
        self.functions.get(name)
    }

    pub fn register(&mut self, name: &str, func: NativeFunction) {
        self.functions.insert(name.to_string(), func);
    }

    fn register_io_functions(&mut self) {
        self.register("print", native_print);
    }
}

fn native_print(args: &[Value]) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Null);
    }

    let output = args[0].format();
    print!("{output}");
    io::stdout().flush()?;
    Ok(Value::Null)
}
