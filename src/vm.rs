use anyhow::{Result, bail};

use crate::{
    bytecode::{BytecodeFile, Constant, Opcode},
    heap::{Heap, HeapPtr},
    native::NativeRegistry,
};

#[derive(Clone, Debug)]
pub enum Value {
    Integer(i64),
    Boolean(bool),
    String(String),
    Reference(RefHandle),
    HeapRef(HeapPtr),
    Null,
}

#[derive(Clone, Debug)]
pub struct RefHandle {
    pub frame_idx: usize,
    pub local_idx: usize,
    pub mutable: bool,
}

impl Value {
    fn as_i64(&self) -> Result<i64> {
        match self {
            Value::Integer(val) => Ok(*val),
            Value::Boolean(val) => Ok(if *val { 1 } else { 0 }),
            _ => bail!("Unable to convert from {self:?} to an Integer"),
        }
    }

    fn as_bool(&self) -> Result<bool> {
        match self {
            Value::Boolean(val) => Ok(*val),
            Value::Integer(val) => Ok(*val != 0),
            _ => bail!("Unable to convert from {self:?} to a Boolean"),
        }
    }

    pub fn format(&self) -> String {
        match self {
            Value::Integer(n) => n.to_string(),
            Value::Boolean(b) => b.to_string(),
            Value::String(s) => s.clone(),
            Value::Null => "null".to_string(),
            Value::Reference(h) => format!(
                "&{}(frame: {}, local: {})",
                if h.mutable { "mut " } else { "" },
                h.frame_idx,
                h.local_idx
            ),
            Value::HeapRef(ptr) => format!("Box({ptr})"),
        }
    }
}

#[derive(Default, Debug)]
pub struct VM {
    bytecode: BytecodeFile,
    stack: Vec<Value>,
    pc: usize,
    running: bool,
    native_registry: NativeRegistry,
    call_stack: Vec<CallFrame>,
    current_function: usize,
    current_frame_id: usize,
    next_frame_id: usize,
    heap: Heap,
}

#[derive(Debug)]
struct CallFrame {
    function_index: usize,
    return_pc: usize,
    locals: Vec<Value>,
    frame_id: usize,
}

impl VM {
    pub fn new(bytecode: BytecodeFile) -> Self {
        Self {
            bytecode,
            ..Default::default()
        }
    }

    pub fn run(&mut self) -> Result<()> {
        let entry_idx = self.bytecode.entrypoint as usize;
        if entry_idx >= self.bytecode.functions.len() {
            bail!("Invalid entry point")
        }

        self.running = true;

        let main_func = &self.bytecode.functions[entry_idx].clone();

        self.current_frame_id = self.next_frame_id;
        self.next_frame_id += 1;

        self.call_stack.push(CallFrame {
            function_index: entry_idx,
            return_pc: 0,
            locals: vec![Value::Null; main_func.locals_count as usize],
            frame_id: self.current_frame_id,
        });

        self.current_function = entry_idx;

        self.stack = Vec::with_capacity(main_func.max_stack as usize);

        self.execute_function()?;
        Ok(())
    }

    fn current_frame(&self) -> &CallFrame {
        self.call_stack.last().expect("No call frame")
    }

    fn current_frame_mut(&mut self) -> &mut CallFrame {
        self.call_stack.last_mut().expect("No call frame")
    }

    fn execute_function(&mut self) -> Result<()> {
        let func = self.bytecode.functions[self.current_function].clone();
        let code = &func.code;

        let heap_scope = self.heap.enter_scope();

        while self.pc < code.len() {
            let opcode = code[self.pc];
            self.pc += 1;

            match Opcode::try_from(opcode) {
                Ok(Opcode::Nop) => {
                    // Do nothing
                }
                Ok(Opcode::Pop) => {
                    self.stack.pop();
                }
                Ok(Opcode::Dup) => {
                    let val = self
                        .stack
                        .last()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?
                        .clone();
                    self.stack.push(val);
                }
                Ok(Opcode::ConstI64) => {
                    let index = self.read_u32(code)?;
                    let constant = &self.bytecode.const_pool[index as usize];
                    if let Constant::Int(n) = constant {
                        self.stack.push(Value::Integer(*n));
                    } else {
                        bail!("Expected Integer constant");
                    }
                }
                Ok(Opcode::ConstString) => {
                    let index = self.read_u32(code)?;
                    let constant = &self.bytecode.const_pool[index as usize];
                    if let Constant::String(s) = constant {
                        self.stack.push(Value::String(s.clone()));
                    } else {
                        bail!("Expected string constant");
                    }
                }
                Ok(Opcode::TinyInt) => {
                    let val = self.read_byte(code)?;
                    self.stack.push(Value::Integer(val as i64));
                }
                Ok(Opcode::LoadLocal) => {
                    let index = self.read_u16(code)? as usize;
                    if index >= self.current_frame().locals.len() {
                        bail!("Invalid local variable index: {index}");
                    }
                    self.stack.push(self.current_frame().locals[index].clone());
                }
                Ok(Opcode::StoreLocal) => {
                    let index = self.read_u16(code)? as usize;
                    if index >= self.current_frame().locals.len() {
                        bail!("Invalid local variable index: {index}");
                    }
                    let value = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    self.current_frame_mut().locals[index] = value;
                }

                Ok(Opcode::Add) => self.binary_op(|a, b| a + b)?,
                Ok(Opcode::Sub) => self.binary_op(|a, b| a - b)?,
                Ok(Opcode::Mul) => self.binary_op(|a, b| a * b)?,
                Ok(Opcode::Div) => self.binary_op(|a, b| a / b)?,
                Ok(Opcode::Mod) => self.binary_op(|a, b| a % b)?,

                Ok(Opcode::And) => self.comparison_op(|a, b| a != 0 && b != 0)?,
                Ok(Opcode::Or) => self.comparison_op(|a, b| a != 0 || b != 0)?,
                Ok(Opcode::Not) => self.unary_op(|a| !a)?,

                Ok(Opcode::Eq) => self.comparison_op(|a, b| a == b)?,
                Ok(Opcode::Ne) => self.comparison_op(|a, b| a != b)?,
                Ok(Opcode::Gt) => self.comparison_op(|a, b| a > b)?,
                Ok(Opcode::Lt) => self.comparison_op(|a, b| a < b)?,
                Ok(Opcode::Gte) => self.comparison_op(|a, b| a >= b)?,
                Ok(Opcode::Lte) => self.comparison_op(|a, b| a <= b)?,

                Ok(Opcode::Jump) => {
                    let loc = self.read_u32(code)? as usize;
                    if loc > code.len() - 1 {
                        bail!("Invalid jump address");
                    }
                    self.pc = loc;
                }
                Ok(Opcode::Call) => self.execute_call(code)?,
                Ok(Opcode::Ret) => {
                    self.execute_return()?;
                    return Ok(());
                }
                Ok(Opcode::CallNative) => self.execute_native_call(code)?,
                Ok(Opcode::CondJump) => {
                    let loc = self.read_u32(code)? as usize;
                    if loc > code.len() - 1 {
                        bail!("Invalid jump address");
                    }

                    let cond = self
                        .stack
                        .pop()
                        .expect("Conditional Jump requires at least one value on the stack.")
                        .as_bool()
                        .unwrap();

                    if cond {
                        self.pc = loc;
                    }
                }

                Ok(Opcode::LoadRef) => {
                    let index = self.read_u16(code)? as usize;
                    let is_mutable = self.read_byte(code)? != 0;

                    let frame = self.current_frame();
                    if index > frame.locals.len() {
                        bail!("Invalid local variable index: {index}");
                    }

                    self.stack.push(Value::Reference(RefHandle {
                        frame_idx: frame.frame_id,
                        local_idx: index,
                        mutable: is_mutable,
                    }))
                }
                Ok(Opcode::LoadRefValue) => {
                    let ref_val = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;

                    if let Value::Reference(handle) = ref_val {
                        let value = self
                            .call_stack
                            .iter()
                            .find(|f| f.frame_id == handle.frame_idx)
                            .ok_or_else(|| anyhow::anyhow!("Reference to invalid frame"))?
                            .locals[handle.local_idx]
                            .clone();

                        self.stack.push(value);
                    } else {
                        bail!("Expected reference, got: {ref_val:?}");
                    }
                }
                Ok(Opcode::StoreRef) => {
                    let ref_val = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    let value = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;

                    if let Value::Reference(handle) = ref_val {
                        if !handle.mutable {
                            bail!("Cannot mutate through immutable reference");
                        }

                        let frame = self
                            .call_stack
                            .iter_mut()
                            .find(|f| f.frame_id == handle.frame_idx)
                            .ok_or_else(|| anyhow::anyhow!("Reference to invalid frame"))?;
                        frame.locals[handle.local_idx] = value;
                    } else {
                        bail!("Expected reference, got: {ref_val:?}");
                    }
                }

                Ok(Opcode::HeapAlloc) => {
                    let value = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    let ptr = self.heap.allocate(value);
                    self.stack.push(Value::HeapRef(ptr));
                }
                Ok(Opcode::HeapLoad) => {
                    let ptr_val = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    if let Value::HeapRef(ptr) = ptr_val {
                        let value = self
                            .heap
                            .get(ptr)
                            .ok_or_else(|| anyhow::anyhow!("Invalid heap pointer"))?
                            .clone();
                        self.stack.push(value);
                    } else {
                        bail!("Expected heap reference");
                    }
                }
                Ok(Opcode::HeapStore) => {
                    let ptr_val = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    let value = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    if let Value::HeapRef(ptr) = ptr_val {
                        self.heap.set(ptr, value)?;
                    } else {
                        bail!("Expected heap reference");
                    }
                }
                Ok(Opcode::HeapFree) => {
                    let ptr_val = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    if let Value::HeapRef(ptr) = ptr_val {
                        self.heap.free(ptr)?;
                    } else {
                        bail!("Expected heap reference");
                    }
                }

                Err(_) => bail!("Unknown opcode: {opcode}"),
            }
        }

        self.heap.exit_scope(heap_scope);

        Ok(())
    }

    fn execute_call(&mut self, code: &[u8]) -> Result<()> {
        let func_idx = self.read_u32(code)? as usize;
        let arity = code[self.pc];
        self.pc += 1;

        if func_idx >= self.bytecode.functions.len() {
            bail!("Invalid function index: {func_idx}");
        }

        let func = &self.bytecode.functions[func_idx];

        if arity != func.arity {
            bail!(
                "Function '{}' expects {} arguments, got {}",
                func.name,
                func.arity,
                arity
            );
        }

        let mut args = Vec::with_capacity(arity as usize);
        for _ in 0..arity {
            args.push(
                self.stack
                    .pop()
                    .ok_or_else(|| anyhow::anyhow!("Stack underflow when popping arguments"))?,
            );
        }
        args.reverse();

        let frame_id = self.next_frame_id;
        self.next_frame_id += 1;

        let mut new_locals = args;
        while new_locals.len() < func.locals_count as usize {
            new_locals.push(Value::Null);
        }

        self.call_stack.push(CallFrame {
            function_index: func_idx,
            return_pc: self.pc,
            locals: new_locals,
            frame_id,
        });

        self.current_function = func_idx;
        self.current_frame_id = frame_id;
        self.pc = 0;

        self.execute_function()?;

        Ok(())
    }

    fn execute_native_call(&mut self, code: &[u8]) -> Result<()> {
        let func_idx = self.read_u32(code)? as usize;
        let func_const = self.bytecode.const_pool[func_idx].clone();
        if let Constant::String(func_name) = func_const {
            let native_func = &self
                .native_registry
                .get(&func_name)
                .ok_or_else(|| anyhow::anyhow!("Unknown native function: {func_name}"))?
                .clone();

            let arity = self.read_byte(code)? as usize;
            let mut args = Vec::with_capacity(arity);
            for _ in 0..arity {
                args.push(
                    self.stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?,
                );
            }
            args.reverse();

            let result = native_func.0(&args)?;

            if !matches!(result, Value::Null) {
                self.stack.push(result);
            }

            Ok(())
        } else {
            bail!("Native function identifier must be a string, got: {func_const:?}")
        }
    }

    fn execute_return(&mut self) -> Result<()> {
        let return_value = if !self.stack.is_empty() {
            Some(self.stack.pop().unwrap())
        } else {
            None
        };

        let old_frame = self.call_stack.pop().unwrap();

        if let Some(frame) = self.call_stack.last() {
            self.current_function = frame.function_index;
            self.current_frame_id = frame.frame_id;
            self.pc = old_frame.return_pc;

            if let Some(val) = return_value {
                self.stack.push(val);
            }
        }

        Ok(())
    }
    fn binary_op<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(i64, i64) -> i64,
    {
        let b = self
            .stack
            .pop()
            .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
        let a = self
            .stack
            .pop()
            .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;

        let result = f(a.as_i64()?, b.as_i64()?);
        self.stack.push(Value::Integer(result));
        Ok(())
    }

    fn comparison_op<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(i64, i64) -> bool,
    {
        let b = self
            .stack
            .pop()
            .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
        let a = self
            .stack
            .pop()
            .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;

        let result = f(a.as_i64()?, b.as_i64()?);
        self.stack.push(Value::Boolean(result));
        Ok(())
    }

    fn unary_op<F>(&mut self, f: F) -> Result<()>
    where
        F: FnOnce(i64) -> i64,
    {
        let a = self
            .stack
            .pop()
            .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;

        let result = f(a.as_i64()?);
        self.stack.push(Value::Integer(result));
        Ok(())
    }

    fn read_byte(&mut self, code: &[u8]) -> Result<u8> {
        if self.pc + 1 > code.len() {
            bail!("Unexpected end of bytecode");
        }
        self.pc += 1;
        Ok(code[self.pc - 1])
    }

    fn read_u16(&mut self, code: &[u8]) -> Result<u16> {
        if self.pc + 2 > code.len() {
            bail!("Unexpected end of bytecode");
        }
        let bytes = [code[self.pc], code[self.pc + 1]];
        self.pc += 2;
        Ok(u16::from_le_bytes(bytes))
    }

    fn read_u32(&mut self, code: &[u8]) -> Result<u32> {
        if self.pc + 4 > code.len() {
            bail!("Unexpected end of bytecode");
        }
        let bytes = [
            code[self.pc],
            code[self.pc + 1],
            code[self.pc + 2],
            code[self.pc + 3],
        ];
        self.pc += 4;
        Ok(u32::from_le_bytes(bytes))
    }
}
