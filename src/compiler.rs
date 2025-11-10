use std::collections::HashMap;

use anyhow::{Ok, Result};

use crate::{
    bytecode::{BytecodeFile, Constant, Function, Opcode},
    parser::AstNode,
};

pub struct Compiler {
    bytecode: BytecodeFile,
    current_function: Function,
    locals: HashMap<String, u16>,
    next_local: u16,
    max_stack: u16,
    current_stack_depth: u16,
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler {
            bytecode: BytecodeFile::new(0),
            current_function: Function {
                name: "main".to_string(),
                arity: 0,
                locals_count: 0,
                max_stack: 0,
                code: Vec::new(),
            },
            locals: HashMap::new(),
            next_local: 0,
            max_stack: 0,
            current_stack_depth: 0,
        }
    }
}

impl Compiler {
    pub fn new(file: BytecodeFile) -> Self {
        Compiler {
            bytecode: file,
            ..Default::default()
        }
    }

    pub fn compile(&mut self, ast: Vec<AstNode>) -> Result<BytecodeFile> {
        for node in ast {
            self.compile_node(node)?;
        }

        self.emit_opcode(Opcode::Ret);

        self.current_function.locals_count = self.next_local;
        self.current_function.max_stack = self.max_stack;

        self.bytecode.functions.push(self.current_function.clone());

        Ok(self.bytecode.clone())
    }

    fn compile_node(&mut self, node: AstNode) -> Result<()> {
        match node {
            AstNode::Number(val) => self.compile_number(val)?,
            AstNode::Ident(ident) => self.compile_load_var(&ident)?,
            AstNode::BinaryOp(left, op, right) => self.compile_binary_op(*left, &op, *right)?,
            AstNode::Let(name, expr) => self.compile_let(&name, *expr)?,
            AstNode::Print(expr) => self.compile_function_call("print", vec![*expr])?,
        }
        Ok(())
    }

    fn compile_number(&mut self, val: i64) -> Result<()> {
        let index = self.add_constant(Constant::Int(val));
        self.emit_opcode(Opcode::ConstI64);
        self.emit_u32(index);
        self.push_stack();
        Ok(())
    }

    fn compile_load_var(&mut self, ident: &str) -> Result<()> {
        let local_idx = *self
            .locals
            .get(ident)
            .ok_or_else(|| anyhow::anyhow!("Undefined variable: {ident}"))?;
        self.emit_opcode(Opcode::LoadLocal);
        self.emit_u16(local_idx);
        self.push_stack();
        Ok(())
    }

    fn compile_binary_op(&mut self, left: AstNode, op: &str, right: AstNode) -> Result<()> {
        self.compile_node(left)?;
        self.compile_node(right)?;

        match op {
            "+" => self.emit_opcode(Opcode::Add),
            "-" => self.emit_opcode(Opcode::Sub),
            _ => anyhow::bail!("Unknown operator: {op}"),
        }

        self.pop_stack();
        Ok(())
    }

    fn compile_let(&mut self, name: &str, expr: AstNode) -> Result<()> {
        let local_idx = if let Some(&idx) = self.locals.get(name) {
            idx
        } else {
            let idx = self.next_local;
            self.locals.insert(name.to_string(), idx);
            self.next_local += 1;
            idx
        };

        self.compile_node(expr)?;

        self.emit_opcode(Opcode::StoreLocal);
        self.emit_u16(local_idx);

        self.pop_stack();
        Ok(())
    }

    fn compile_function_call(&mut self, name: &str, args: Vec<AstNode>) -> Result<()> {
        if Self::is_native(name) {
            self.compile_native_call(name, args)
        } else {
            anyhow::bail!("User defined function calls are not yet supported");
        }
    }

    fn compile_native_call(&mut self, name: &str, args: Vec<AstNode>) -> Result<()> {
        // TODO: Fix xD
        let name_idx = self.add_constant(Constant::String(name.to_string()));

        for arg in args.iter() {
            self.compile_node(arg.clone())?;
            self.pop_stack();
        }

        self.emit_opcode(Opcode::Call);
        self.emit_u32(name_idx);

        self.push_stack();

        Ok(())
    }

    fn is_native(name: &str) -> bool {
        matches!(name, "print")
    }

    fn add_constant(&mut self, constant: Constant) -> u32 {
        let index = self.bytecode.const_pool.len();
        self.bytecode.const_pool.push(constant);
        index as u32
    }

    fn emit_opcode(&mut self, opcode: Opcode) {
        self.current_function.code.push(opcode as u8);
    }

    fn emit_byte(&mut self, val: u8) {
        self.current_function.code.push(val);
    }

    fn emit_u16(&mut self, val: u16) {
        self.current_function
            .code
            .extend_from_slice(&val.to_le_bytes());
    }

    fn emit_u32(&mut self, val: u32) {
        self.current_function
            .code
            .extend_from_slice(&val.to_le_bytes());
    }

    fn push_stack(&mut self) {
        self.current_stack_depth += 1;
        if self.current_stack_depth > self.max_stack {
            self.max_stack = self.current_stack_depth;
        }
    }

    fn pop_stack(&mut self) {
        if self.current_stack_depth > 0 {
            self.current_stack_depth -= 1;
        }
    }
}
