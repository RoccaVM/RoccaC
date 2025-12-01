use std::{
    collections::HashMap,
    io::{self, Write},
};

use anyhow::{Result, bail};

use crate::{
    types::Type,
    vm::{VM, Value},
};

pub type NativeFunction = fn(&mut VM, &[Value]) -> Result<Value>;

// (fn, artiy, vararg, return_type)
pub type NativeFnDesc = (NativeFunction, u8, bool, Type);

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
        registry.register_memory_functions();

        registry
    }

    pub fn get(&self, name: &str) -> Option<&NativeFnDesc> {
        self.functions.get(name)
    }

    pub fn register(&mut self, name: &str, func: NativeFnDesc) {
        self.functions.insert(name.to_string(), func);
    }

    fn register_io_functions(&mut self) {
        self.register("print", (native_print, 1, true, Type::Unit));
    }

    fn register_memory_functions(&mut self) {
        self.register("box", (native_box, 1, false, Type::Unknown));
        self.register("drop", (native_drop, 1, false, Type::Unit));
    }

    pub fn has(&self, name: &str) -> bool {
        self.functions.contains_key(name)
    }
}

fn native_print(_vm: &mut VM, args: &[Value]) -> Result<Value> {
    if args.is_empty() {
        return Ok(Value::Null);
    }

    let output: Vec<String> = args.iter().map(|a| a.format()).collect();
    print!("{}", output.join(" "));
    io::stdout().flush()?;
    Ok(Value::Null)
}

fn native_box(vm: &mut VM, args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        bail!("box() expects exactly one argument");
    }

    let value = args[0].clone();
    let ptr = vm.heap_allocate(value);
    Ok(Value::HeapRef(ptr))
}

fn native_drop(vm: &mut VM, args: &[Value]) -> Result<Value> {
    if args.len() != 1 {
        bail!("drop() expects exactly one argument");
    }

    if let Value::HeapRef(ptr) = &args[0] {
        vm.heap_free(*ptr).map_err(|e| anyhow::anyhow!(e))?;
        Ok(Value::Null)
    } else {
        bail!("drop() expects a Box value");
    }
}
