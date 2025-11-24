use std::{collections::HashMap, fs};

use anyhow::{Result, bail};
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

use crate::{
    bytecode::{BytecodeFile, Constant, Function, Opcode},
    native::NativeRegistry,
    parser::{AstNode, Loc},
    registry::SymbolRegistry,
    types::{Mutability, Type},
};

pub struct Compiler {
    bytecode: BytecodeFile,
    current_function: Option<Function>,
    // Name, (Type, ID, mutability, definition location)
    locals: HashMap<String, (Type, u16, bool, Loc)>,
    next_local: u16,
    max_stack: u16,
    current_stack_depth: u16,

    native_registry: NativeRegistry,
    symbol_registry: SymbolRegistry,
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler {
            bytecode: BytecodeFile::new(0),
            current_function: None,
            locals: HashMap::new(),
            next_local: 0,
            max_stack: 0,
            current_stack_depth: 0,

            native_registry: NativeRegistry::new(),
            symbol_registry: SymbolRegistry::new(),
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
        for node in ast.clone() {
            self.symbol_registry.traverse(node)?;
        }

        for node in ast {
            self.compile_node(node)?;
        }

        if let Some(current_function) = &mut self.current_function {
            current_function.locals_count = self.next_local;
            current_function.max_stack = self.max_stack;

            self.bytecode.functions.push(current_function.clone());
        }

        Ok(self.bytecode.clone())
    }

    fn compile_node(&mut self, node: AstNode) -> Result<Type> {
        match node {
            AstNode::Number(val, loc) => self.compile_number(val, loc),
            AstNode::String(val, loc) => self.compile_string(val, loc),
            AstNode::Ident(ident, loc) => self.compile_load_var(&ident, loc),
            AstNode::BinaryOp(left, op, right, loc) => {
                self.compile_binary_op(*left, &op, *right, loc)
            }
            AstNode::UnaryOp(n, op, loc) => self.compile_unary_op(*n, &op, loc),
            AstNode::Comparison(left, op, right, loc) => {
                self.compile_comparison(*left, &op, *right, loc)
            }
            AstNode::Let(name, mutability, data_type, expr, loc) => {
                self.compile_let(&name, mutability, data_type, *expr, loc)
            }
            AstNode::Assign(name, expr, loc) => self.compile_assign(*name, *expr, loc),
            AstNode::Call(name, args, loc) => self.compile_function_call(&name, args, loc),
            AstNode::Return(expr, loc) => self.compile_return(expr, loc),
            AstNode::FnDef(name, args, return_type, body, loc) => {
                self.compile_function_def(&name, args, return_type, body, loc)
            }
            AstNode::If(conditional, unconditional, loc) => {
                self.compile_if(conditional, unconditional, loc)
            }
            AstNode::While(cond, stmts, loc) => self.compile_while(*cond, stmts, loc),
            AstNode::Ref(expr, mutable, loc) => self.compile_ref(*expr, mutable, loc),
            AstNode::Deref(expr, loc) => self.compile_deref(*expr, loc),
        }
    }

    fn compile_number(&mut self, val: i64, _loc: Loc) -> Result<Type> {
        let index = self.add_constant(Constant::Int(val));
        self.emit_opcode(Opcode::ConstI64);
        self.emit_u32(index);
        self.push_stack();
        Ok(Type::Int)
    }

    fn compile_string(&mut self, val: String, _loc: Loc) -> Result<Type> {
        let index = self.add_constant(Constant::String(val));
        self.emit_opcode(Opcode::ConstString);
        self.emit_u32(index);
        self.push_stack();
        Ok(Type::String)
    }

    fn compile_load_var(&mut self, ident: &str, loc: Loc) -> Result<Type> {
        let local_idx = self
            .locals
            .get(ident)
            .ok_or_else(|| {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!("Variable {ident:?} not found"))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message(format!("Could not find a variable named {ident:?}"))
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                anyhow::anyhow!("Varaible {ident:?} not found")
            })?
            .clone();
        self.emit_opcode(Opcode::LoadLocal);
        self.emit_u16(local_idx.1);
        self.push_stack();
        Ok(local_idx.0)
    }

    fn compile_binary_op(
        &mut self,
        left: AstNode,
        op: &str,
        right: AstNode,
        loc: Loc,
    ) -> Result<Type> {
        self.compile_node(left)?;
        self.compile_node(right)?;

        match op {
            "+" => self.emit_opcode(Opcode::Add),
            "-" => self.emit_opcode(Opcode::Sub),
            "*" => self.emit_opcode(Opcode::Mul),
            "/" => self.emit_opcode(Opcode::Div),
            "&&" => self.emit_opcode(Opcode::And),
            "||" => self.emit_opcode(Opcode::Or),
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!("Unknown operator '{op}'"))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message("Unknown operator used here")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Unknown operator '{op}'");
            }
        }

        self.pop_stack();
        Ok(Type::Int)
    }

    fn compile_unary_op(&mut self, n: AstNode, op: &str, loc: Loc) -> Result<Type> {
        match op {
            "-" => {
                self.emit_opcode(Opcode::TinyInt);
                self.emit_byte(0);
                self.push_stack();
                self.compile_node(n)?;
                self.emit_opcode(Opcode::Sub);
                self.pop_stack();
                Ok(Type::Int)
            }
            "!" => {
                self.compile_node(n)?;
                self.emit_opcode(Opcode::Not);
                Ok(Type::Int)
            }
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!("Unknown operator '{op}'"))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message("Unknown operator used here")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Unknown operator '{op}'");
            }
        }
    }

    fn compile_comparison(
        &mut self,
        left: AstNode,
        op: &str,
        right: AstNode,
        loc: Loc,
    ) -> Result<Type> {
        self.compile_node(left)?;
        self.compile_node(right)?;

        match op {
            ">" => self.emit_opcode(Opcode::Gt),
            "<" => self.emit_opcode(Opcode::Lt),
            "==" => self.emit_opcode(Opcode::Eq),
            "!=" => self.emit_opcode(Opcode::Ne),
            ">=" => self.emit_opcode(Opcode::Gte),
            "<=" => self.emit_opcode(Opcode::Lte),
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!("Unknown comparator '{op}'"))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message("Unknown comparator used here")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Unknown comparator '{op}'");
            }
        }

        Ok(Type::Bool)
    }

    fn compile_let(
        &mut self,
        name: &str,
        mutability: bool,
        data_type: Option<(String, Loc)>,
        expr: AstNode,
        loc: Loc,
    ) -> Result<Type> {
        if let Some(local_idx) = self.locals.get(name) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();
            Report::build(ReportKind::Error, loc.clone())
                .with_message(format!("Variable {name} already defined"))
                .with_label(
                    Label::new(local_idx.3.clone())
                        .with_message("Varaible already defined here")
                        .with_color(b),
                )
                .with_label(
                    Label::new(loc.clone())
                        .with_message("Variable redefined here")
                        .with_color(a),
                )
                .with_help("Either mutate the first definition or rename the second one.")
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Variable {name} already defined");
        }

        let local_idx = {
            let idx = self.next_local;
            let data_type = if let Some(data_type) = data_type.clone() {
                Type::from_string(data_type.0)?
            } else {
                Type::infer(expr.clone())?
            };
            self.locals.insert(
                name.to_string(),
                (data_type.clone(), idx, mutability, loc.clone()),
            );
            self.next_local += 1;
            (data_type, idx)
        };

        let actual_type = self.compile_node(expr.clone())?;
        if !actual_type.can_convert_to(local_idx.0.clone()) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let mut builder = Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Unable to convert from {actual_type:?} to {:?}",
                    local_idx.0
                ))
                .with_label(
                    Label::new(expr.loc())
                        .with_message(format!("Expression has type {actual_type:?}"))
                        .with_color(a),
                );

            if let Some(data_type) = data_type {
                let b = colors.next();
                builder = builder
                    .with_label(
                        Label::new(data_type.1)
                            .with_message(format!(
                                "Expected type {:?}",
                                Type::from_string(data_type.0.clone())?
                            ))
                            .with_color(b),
                    )
                    .with_help(format!(
                        "Remove the type specifier or replace it with '{:?}'",
                        Type::from_string(data_type.0)?
                    ));
            }

            builder
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!(
                "Unable to convert from {actual_type:?} to {:?}",
                local_idx.0
            );
        }

        self.emit_opcode(Opcode::StoreLocal);
        self.emit_u16(local_idx.1);

        self.pop_stack();
        Ok(Type::Unit)
    }

    fn compile_assign(&mut self, name: AstNode, expr: AstNode, loc: Loc) -> Result<Type> {
        match name {
            AstNode::Ident(n, _) => {
                let name = &n;
                let local_idx = self
                    .locals
                    .get(name)
                    .ok_or_else(|| {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        Report::build(ReportKind::Error, loc.clone())
                            .with_message(format!("Variable {name:?} not found"))
                            .with_label(
                                Label::new(loc.clone())
                                    .with_message(format!(
                                        "Could not find a variable named {name:?}"
                                    ))
                                    .with_color(a),
                            )
                            .finish()
                            .print((
                                loc.0.clone(),
                                Source::from(fs::read_to_string(loc.0.clone()).unwrap()),
                            ))
                            .unwrap();
                        anyhow::anyhow!("Varaible {name:?} not found")
                    })?
                    .clone();

                let actual_type = self.compile_node(expr.clone())?;
                if !actual_type.can_convert_to(local_idx.0.clone()) {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Unable to convert from {actual_type:?} to {:?}",
                            local_idx.0
                        ))
                        .with_label(
                            Label::new(local_idx.3.clone())
                                .with_message(format!("Expected type {:?}", local_idx.0))
                                .with_color(b),
                        )
                        .with_label(
                            Label::new(expr.loc())
                                .with_message(format!("Expression has type {actual_type:?}"))
                                .with_color(a),
                        )
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(loc.0).unwrap()),
                        ))
                        .unwrap();
                    bail!(
                        "Unable to convert from {actual_type:?} to {:?}",
                        local_idx.0
                    );
                }

                if !local_idx.2 {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!("Variable {name} is immutable"))
                        .with_label(
                            Label::new(local_idx.3)
                                .with_message("Variable was not defined as mutable")
                                .with_color(b),
                        )
                        .with_label(
                            Label::new(loc.clone())
                                .with_message("Variable must be mutable to allow assignment")
                                .with_color(a),
                        )
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(loc.0).unwrap()),
                        ))
                        .unwrap();
                    bail!("Variable {name} is immutable");
                }

                self.emit_opcode(Opcode::StoreLocal);
                self.emit_u16(local_idx.1);

                self.pop_stack();
                Ok(Type::Unit)
            }
            AstNode::Deref(node, loc) => {
                let node_loc = node.loc();
                let actual_type = self.compile_node(expr.clone())?;
                let expr_type = self.compile_node(*node)?;
                match expr_type.clone() {
                    Type::Reference(inner, mutable) => match mutable {
                        Mutability::Mutable => {
                            if !actual_type.can_convert_to(*inner.clone()) {
                                let mut colors = ColorGenerator::new();
                                let a = colors.next();
                                let b = colors.next();
                                Report::build(ReportKind::Error, loc.clone())
                                    .with_message(format!(
                                        "Unable to convert from {actual_type:?} to {inner:?}"
                                    ))
                                    .with_label(
                                        Label::new(loc.clone())
                                            .with_message(format!("Expected type {inner:?}"))
                                            .with_color(b),
                                    )
                                    .with_label(
                                        Label::new(expr.loc())
                                            .with_message(format!(
                                                "Expression has type {actual_type:?}"
                                            ))
                                            .with_color(a),
                                    )
                                    .finish()
                                    .print((
                                        loc.0.clone(),
                                        Source::from(fs::read_to_string(loc.0).unwrap()),
                                    ))
                                    .unwrap();
                                bail!("Unable to convert from {actual_type:?} to {inner:?}");
                            }
                            self.emit_opcode(Opcode::StoreRef);
                            Ok(Type::Unit)
                        }
                        Mutability::Immutable => {
                            let mut colors = ColorGenerator::new();
                            let a = colors.next();
                            Report::build(ReportKind::Error, loc.clone())
                                .with_message(
                                    "Cannot dereference non-reference type: {expr_type:?}",
                                )
                                .with_label(
                                    Label::new(node_loc)
                                        .with_message("This expression has type {expr_type:?}")
                                        .with_color(a),
                                )
                                .finish()
                                .print((
                                    loc.0.clone(),
                                    Source::from(fs::read_to_string(loc.0).unwrap()),
                                ))
                                .unwrap();
                            bail!("Cannot dereference non-reference type: {expr_type:?}");
                        }
                    },
                    _ => {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        Report::build(ReportKind::Error, loc.clone())
                            .with_message("Cannot dereference non-reference type: {expr_type:?}")
                            .with_label(
                                Label::new(node_loc)
                                    .with_message("This expression has type {expr_type:?}")
                                    .with_color(a),
                            )
                            .finish()
                            .print((
                                loc.0.clone(),
                                Source::from(fs::read_to_string(loc.0).unwrap()),
                            ))
                            .unwrap();
                        bail!("Cannot dereference non-reference type: {expr_type:?}");
                    }
                }
            }
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Assignment is only possible to an Ident or a Reference, got: {name:?}"
                    ))
                    .with_label(
                        Label::new(name.loc())
                            .with_message("Node is of type: {name:?}")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Assignment is only possible to an Ident or a Reference, got: {name:?}");
            }
        }
    }

    fn compile_ref(&mut self, expr: AstNode, mutable: bool, loc: Loc) -> Result<Type> {
        match expr.clone() {
            AstNode::Ident(name, ident_loc) => {
                let var = self
                    .locals
                    .get(&name)
                    .ok_or_else(|| {
                        let mut colors = ColorGenerator::new();
                        let a = colors.next();
                        Report::build(ReportKind::Error, ident_loc.clone())
                            .with_message(format!("Variable {name:?} not found"))
                            .with_label(
                                Label::new(ident_loc.clone())
                                    .with_message(format!("Could not find variable {name:?}"))
                                    .with_color(a),
                            )
                            .finish()
                            .print((
                                ident_loc.0.clone(),
                                Source::from(fs::read_to_string(ident_loc.0).unwrap()),
                            ))
                            .unwrap();
                        anyhow::anyhow!("Variable {name:?} not found")
                    })?
                    .clone();

                if mutable && !var.2 {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Cannot take mutable reference to immutable variable {name}"
                        ))
                        .with_label(
                            Label::new(var.3.clone())
                                .with_message("Variable defined as immutable here")
                                .with_color(b),
                        )
                        .with_label(
                            Label::new(loc.clone())
                                .with_message("Attempting to take mutable reference here")
                                .with_color(a),
                        )
                        .with_help("Change the variable to be mutable with 'let mut'")
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(loc.0).unwrap()),
                        ))
                        .unwrap();
                    bail!("Cannot take mutable reference to immutable variable");
                }

                self.emit_opcode(Opcode::LoadRef);
                self.emit_u16(var.1);
                self.emit_byte(if mutable { 1 } else { 0 });
                self.push_stack();

                Ok(Type::Reference(
                    Box::new(var.0.clone()),
                    if mutable {
                        Mutability::Mutable
                    } else {
                        Mutability::Immutable
                    },
                ))
            }
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message("Can only take references to variables")
                    .with_label(
                        Label::new(expr.loc())
                            .with_message("Cannot take reference to this expression")
                            .with_color(a),
                    )
                    .with_help("Assign the expression to a variable first, then take a reference")
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Can only take references to variables");
            }
        }
    }

    fn compile_deref(&mut self, expr: AstNode, loc: Loc) -> Result<Type> {
        let expr_type = self.compile_node(expr.clone())?;
        match expr_type {
            Type::Reference(inner, _) => {
                self.emit_opcode(Opcode::LoadRefValue);
                Ok(*inner)
            }
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message("Cannot dereference non-reference type: {expr_type:?}")
                    .with_label(
                        Label::new(expr.loc())
                            .with_message("This expression has type {expr_type:?}")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Cannot dereference non-reference type: {expr_type:?}");
            }
        }
    }

    fn compile_return(&mut self, expr: Option<Box<AstNode>>, loc: Loc) -> Result<Type> {
        let ret_type = if let Some(expr) = expr {
            self.compile_node(*expr)?
        } else {
            Type::Unit
        };

        let cf = self.current_function.as_ref().unwrap();
        let expected_type = self.symbol_registry.get(&cf.name).unwrap();
        if !ret_type.can_convert_to(expected_type.return_type.clone()) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();
            Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Unable to convert from {ret_type:?} to {:?}",
                    expected_type.return_type
                ))
                .with_label(
                    Label::new(expected_type.loc.clone())
                        .with_message(format!("Expected type {:?}", expected_type.return_type))
                        .with_color(b),
                )
                .with_label(
                    Label::new(loc.clone())
                        .with_message(format!("Expression has type {ret_type:?}"))
                        .with_color(a),
                )
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!(
                "Unable to convert from {ret_type:?} to {:?}",
                expected_type.return_type
            );
        }

        self.emit_opcode(Opcode::Ret);
        Ok(Type::Unit)
    }

    fn compile_if(
        &mut self,
        conditional: Vec<(Box<AstNode>, Vec<AstNode>)>,
        unconditional: Vec<AstNode>,
        loc: Loc,
    ) -> Result<Type> {
        let mut write_start_to = Vec::new();
        for branch in conditional.clone() {
            let cond_type = self.compile_node(*branch.0.clone())?;

            if !cond_type.can_convert_to(Type::Bool) {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Unable to convert from {cond_type:?} to {:?}",
                        Type::Bool
                    ))
                    .with_label(
                        Label::new(branch.0.loc())
                            .with_message(format!(
                                "Expression has type {cond_type:?} but Bool was expected"
                            ))
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Unable to convert from {cond_type:?} to {:?}", Type::Bool);
            }

            self.emit_opcode(Opcode::CondJump);
            write_start_to.push(self.current_function.as_ref().unwrap().code.len());
            self.emit_u32(u32::MAX);
        }
        self.emit_opcode(Opcode::Jump);
        write_start_to.push(self.current_function.as_ref().unwrap().code.len());
        self.emit_u32(u32::MAX);

        let mut write_end_to = Vec::new();
        for (i, branch) in conditional.iter().enumerate() {
            let addr_to_write =
                (self.current_function.as_ref().unwrap().code.len() as u32).to_le_bytes();
            let offset = write_start_to[i];
            self.current_function.as_mut().unwrap().code[offset..(4 + offset)]
                .copy_from_slice(&addr_to_write[..4]);

            for node in branch.1.clone() {
                self.compile_node(node)?;
            }

            self.emit_opcode(Opcode::Jump);
            write_end_to.push(self.current_function.as_ref().unwrap().code.len());
            self.emit_u32(u32::MAX);
        }

        let mut addr_to_write = (self.current_function.as_ref().unwrap().code.len()).to_le_bytes();
        let offset = *write_start_to.last().unwrap();
        self.current_function.as_mut().unwrap().code[offset..(4 + offset)]
            .copy_from_slice(&addr_to_write[..4]);

        if !unconditional.is_empty() {
            for node in unconditional {
                self.compile_node(node)?;
            }

            addr_to_write = (self.current_function.as_ref().unwrap().code.len()).to_le_bytes();
        }

        for offset in write_end_to {
            self.current_function.as_mut().unwrap().code[offset..(4 + offset)]
                .copy_from_slice(&addr_to_write[..4]);
        }

        Ok(Type::Unit)
    }

    fn compile_while(&mut self, cond: AstNode, body: Vec<AstNode>, loc: Loc) -> Result<Type> {
        let start = self.current_function.as_ref().unwrap().code.len() as u32;
        let cond_type = self.compile_node(cond.clone())?;
        if !cond_type.can_convert_to(Type::Bool) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Unable to convert from {cond_type:?} to {:?}",
                    Type::Bool
                ))
                .with_label(
                    Label::new(cond.loc())
                        .with_message(format!(
                            "Expression has type {cond_type:?} but Bool was expected"
                        ))
                        .with_color(a),
                )
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Unable to convert from {cond_type:?} to {:?}", Type::Bool);
        }

        self.emit_opcode(Opcode::CondJump);
        self.emit_u32(self.current_function.as_ref().unwrap().code.len() as u32 + 9);
        self.emit_opcode(Opcode::Jump);
        let write_end = self.current_function.as_ref().unwrap().code.len();
        self.emit_u32(u32::MAX);

        for n in body {
            self.compile_node(n)?;
        }

        self.emit_opcode(Opcode::Jump);
        self.emit_u32(start);

        let addr_to_write = (self.current_function.as_ref().unwrap().code.len()).to_le_bytes();
        self.current_function.as_mut().unwrap().code[write_end..(write_end + 4)]
            .copy_from_slice(&addr_to_write[..4]);

        Ok(Type::Unit)
    }

    fn compile_function_def(
        &mut self,
        name: &str,
        args: Vec<(String, String, Loc)>,
        _return_type: Option<String>,
        body: Vec<AstNode>,
        _loc: Loc,
    ) -> Result<Type> {
        if let Some(cf) = self.current_function.clone()
            && cf.code.last().is_none_or(|&op| op != Opcode::Ret as u8)
        {
            self.emit_opcode(Opcode::Ret);
        }

        if let Some(current_function) = &mut self.current_function {
            current_function.locals_count = self.next_local;
            current_function.max_stack = self.max_stack;

            self.bytecode.functions.push(current_function.clone());
        }

        self.current_function = Some(Function {
            name: name.to_string(),
            arity: args.len() as u8,
            locals_count: 0,
            max_stack: 0,
            code: vec![],
        });
        self.locals = HashMap::new();
        self.next_local = 0;

        for arg in args {
            let idx = self.next_local;
            self.locals
                .insert(arg.0, (Type::from_string(arg.1)?, idx, false, arg.2));
            self.next_local += 1;
        }

        for node in body {
            self.compile_node(node)?;
        }

        Ok(Type::Unit)
    }

    fn compile_function_call(&mut self, name: &str, args: Vec<AstNode>, loc: Loc) -> Result<Type> {
        if self.native_registry.has(name) {
            self.compile_native_call(name, args, loc)
        } else {
            let symbol = &self
                .symbol_registry
                .get(name)
                .ok_or_else(|| {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!("Function {name:?} not found"))
                        .with_label(
                            Label::new(loc.clone())
                                .with_message(format!("Could not find a function named {name:?}"))
                                .with_color(a),
                        )
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(loc.0.clone()).unwrap()),
                        ))
                        .unwrap();
                    anyhow::anyhow!("Function {name:?} not found")
                })?
                .clone();

            if (args.len() as u8) != symbol.arity {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                let b = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Expected {:?} arguments, got {:?}",
                        symbol.arity,
                        args.len()
                    ))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message(format!("Calling with {:?} arguments", args.len()))
                            .with_color(a),
                    )
                    .with_label(
                        Label::new(symbol.loc.clone())
                            .with_message(format!("Expected {:?} arguments", symbol.arity))
                            .with_color(b),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!(
                    "Expected {:?} arguments, got {:?}",
                    symbol.arity,
                    args.len()
                );
            }

            for (i, arg) in args.iter().enumerate() {
                let actual_type = self.compile_node(arg.clone())?;
                if !actual_type.can_convert_to(symbol.arg_types[i].0.clone()) {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Unable to convert from {actual_type:?} to {:?}",
                            symbol.arg_types[i].0
                        ))
                        .with_label(
                            Label::new(arg.loc())
                                .with_message(format!("Expression has type {actual_type:?}"))
                                .with_color(a),
                        )
                        .with_label(
                            Label::new(symbol.arg_types[i].1.clone())
                                .with_message(format!("Expected type {:?}", symbol.arg_types[i].0))
                                .with_color(b),
                        )
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(loc.0).unwrap()),
                        ))
                        .unwrap();
                    bail!(
                        "Unable to convert from {actual_type:?} to {:?}",
                        symbol.arg_types[i].0
                    );
                }
                self.pop_stack();
            }

            self.emit_opcode(Opcode::Call);
            self.emit_u32(symbol.index);
            self.emit_byte(args.len() as u8);

            if symbol.returns {
                self.push_stack();
            }

            Ok(symbol.return_type.clone())
        }
    }

    fn compile_native_call(&mut self, name: &str, args: Vec<AstNode>, loc: Loc) -> Result<Type> {
        let (_, arity, vararg, return_type) = self.native_registry.get(name).unwrap().clone();

        if vararg {
            if (args.len() as u8) < arity {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Expected at least {:?} arguments, got {:?}",
                        arity,
                        args.len()
                    ))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message(format!("Calling with {:?} arguments", args.len()))
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Compilation error");
            }
        } else if args.len() as u8 != arity {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Expected {:?} arguments, got {:?}",
                    arity,
                    args.len()
                ))
                .with_label(
                    Label::new(loc.clone())
                        .with_message(format!("Calling with {:?} arguments", args.len()))
                        .with_color(a),
                )
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Compilation error");
        }

        let name_idx = self.add_constant(Constant::String(name.to_string()));

        for arg in args.iter() {
            self.compile_node(arg.clone())?;
            self.pop_stack();
        }

        self.emit_opcode(Opcode::CallNative);
        self.emit_u32(name_idx);
        self.emit_byte(args.len() as u8);

        if !matches!(return_type, Type::Unit) {
            self.push_stack();
        }

        Ok(return_type)
    }

    fn add_constant(&mut self, constant: Constant) -> u32 {
        let index = self.bytecode.const_pool.len();
        self.bytecode.const_pool.push(constant);
        index as u32
    }

    fn emit_opcode(&mut self, opcode: Opcode) {
        self.current_function
            .as_mut()
            .expect("Statement outside function")
            .code
            .push(opcode as u8);
    }

    fn emit_byte(&mut self, val: u8) {
        self.current_function
            .as_mut()
            .expect("Statement outside function")
            .code
            .push(val);
    }

    fn emit_u16(&mut self, val: u16) {
        self.current_function
            .as_mut()
            .expect("Statement outside function")
            .code
            .extend_from_slice(&val.to_le_bytes());
    }

    fn emit_u32(&mut self, val: u32) {
        self.current_function
            .as_mut()
            .expect("Statement outside function")
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
