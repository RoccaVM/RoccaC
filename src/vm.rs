use anyhow::{Result, bail};

use crate::{
    bytecode::{BytecodeFile, Constant, Opcode},
    native::NativeRegistry,
};

#[derive(Clone, Debug)]
pub enum Value {
    Integer(i64),
    Boolean(bool),
    Null,
}

impl Value {
    fn as_i64(&self) -> Result<i64> {
        match self {
            Value::Integer(val) => Ok(*val),
            _ => bail!("Unable to convert from {self:?} to an Integer"),
        }
    }

    pub fn format(&self) -> String {
        match self {
            Value::Integer(n) => n.to_string(),
            Value::Boolean(b) => b.to_string(),
            Value::Null => "null".to_string(),
        }
    }
}

#[derive(Default, Debug)]
pub struct VM {
    bytecode: BytecodeFile,
    stack: Vec<Value>,
    locals: Vec<Value>,
    pc: usize,
    native_registry: NativeRegistry,
    call_stack: Vec<CallFrame>,
    current_function: usize,
}

#[derive(Debug)]
struct CallFrame {
    function_index: usize,
    return_pc: usize,
    locals: Vec<Value>,
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

        let main_func = &self.bytecode.functions[entry_idx].clone();
        self.locals = vec![Value::Null; main_func.locals_count as usize];

        self.current_function = entry_idx;

        self.execute_function()?;
        Ok(())
    }

    fn execute_function(&mut self) -> Result<()> {
        let func = self.bytecode.functions[self.current_function].clone();
        let code = &func.code;

        while self.pc < code.len() {
            let opcode = code[self.pc];
            self.pc += 1;

            match opcode {
                op if op == Opcode::Nop as u8 => {
                    // Do nothing
                }
                op if op == Opcode::Pop as u8 => {
                    self.stack.pop();
                }
                op if op == Opcode::Dup as u8 => {
                    let val = self
                        .stack
                        .last()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?
                        .clone();
                    self.stack.push(val);
                }
                op if op == Opcode::ConstI64 as u8 => {
                    let index = self.read_u32(code)?;
                    let constant = &self.bytecode.const_pool[index as usize];
                    if let Constant::Int(n) = constant {
                        self.stack.push(Value::Integer(*n));
                    } else {
                        bail!("Expected Integer constant");
                    }
                }
                op if op == Opcode::LoadLocal as u8 => {
                    let index = self.read_u16(code)? as usize;
                    if index >= self.locals.len() {
                        bail!("Invalid local variable index: {index}");
                    }
                    self.stack.push(self.locals[index].clone());
                }
                op if op == Opcode::StoreLocal as u8 => {
                    let index = self.read_u16(code)? as usize;
                    if index >= self.locals.len() {
                        bail!("Invalid local variable index: {index}");
                    }
                    let value = self
                        .stack
                        .pop()
                        .ok_or_else(|| anyhow::anyhow!("Stack underflow"))?;
                    self.locals[index] = value;
                }
                op if op == Opcode::Add as u8 => {
                    self.binary_op(|a, b| a + b)?;
                }
                op if op == Opcode::Sub as u8 => {
                    self.binary_op(|a, b| a - b)?;
                }
                op if op == Opcode::And as u8 => {
                    self.comparison_op(|a, b| a != 0 && b != 0)?;
                }
                op if op == Opcode::Or as u8 => {
                    self.comparison_op(|a, b| a != 0 || b != 0)?;
                }
                op if op == Opcode::Not as u8 => {
                    self.bitwise_op(|a| !a)?;
                }
                op if op == Opcode::Eq as u8 => {
                    self.comparison_op(|a, b| a == b)?;
                }
                op if op == Opcode::Ne as u8 => {
                    self.comparison_op(|a, b| a != b)?;
                }
                op if op == Opcode::Jump as u8 => {
                    let loc = self.read_u32(code)? as usize;
                    if loc > code.len() - 1 {
                        bail!("Invalid jump address");
                    }
                    self.pc = loc;
                }
                op if op == Opcode::Call as u8 => {
                    self.execute_call(code)?;
                }
                op if op == Opcode::Ret as u8 => {
                    self.execute_return()?;
                    return Ok(());
                }
                op if op == Opcode::CallNative as u8 => {
                    self.execute_native_call(code)?;
                }
                _ => bail!("Unknown opcode: {opcode}"),
            }
        }

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

        let saved_frame = CallFrame {
            function_index: self.current_function,
            return_pc: self.pc,
            locals: std::mem::take(&mut self.locals),
        };
        self.call_stack.push(saved_frame);

        self.current_function = func_idx;
        self.pc = 0;

        self.locals = args;
        while self.locals.len() < func.locals_count as usize {
            self.locals.push(Value::Null);
        }

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

        if let Some(frame) = self.call_stack.pop() {
            self.current_function = frame.function_index;
            self.pc = frame.return_pc;
            self.locals = frame.locals;

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

    fn bitwise_op<F>(&mut self, f: F) -> Result<()>
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
