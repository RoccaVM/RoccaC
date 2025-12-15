use std::{collections::HashMap, fs};

use anyhow::{Result, bail};
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

use crate::{
    borrow_checker::BorrowChecker,
    bytecode::{BytecodeFile, Constant, Function, Opcode},
    native::NativeRegistry,
    parser::{AstNode, Loc},
    registry::SymbolRegistry,
    scope::{ScopeManager, Variable},
    types::{Field, Mutability, StructDef, Type, TypeRegistry},
};

pub struct Compiler {
    bytecode: BytecodeFile,
    current_function: Option<Function>,
    next_local: u16,
    max_stack: u16,
    current_stack_depth: u16,

    native_registry: NativeRegistry,
    symbol_registry: SymbolRegistry,
    type_registry: TypeRegistry,

    scope_manager: ScopeManager,
    borrow_checker: BorrowChecker,
}

impl Default for Compiler {
    fn default() -> Self {
        Compiler {
            bytecode: BytecodeFile::new(0),
            current_function: None,
            next_local: 0,
            max_stack: 0,
            current_stack_depth: 0,

            native_registry: NativeRegistry::new(),
            symbol_registry: SymbolRegistry::new(),
            type_registry: TypeRegistry::new(),

            scope_manager: ScopeManager::new(),
            borrow_checker: BorrowChecker::new(),
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
            if let AstNode::StructDef(name, type_params, fields, loc) = node {
                self.compile_struct_def(name, type_params, fields, loc)?;
            }
        }

        for node in ast.clone() {
            self.symbol_registry.traverse(node, &self.type_registry)?;
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
            AstNode::Assign(target, expr, loc) => self.compile_assign(*target, *expr, loc),
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
            AstNode::StructDef(_, _, _, _) => Ok(Type::Unit),
            AstNode::StructLiteral(name, field_values, loc) => {
                self.compile_struct_literal(name, field_values, loc)
            }
            AstNode::FieldAccess(struc, field, loc) => {
                self.compile_field_access(*struc, field, loc)
            }
            AstNode::MethodCall(_, _, _, _) => unimplemented!(), // TODO: Implement ionce impls
        }
    }

    fn infer_type(&self, node: &AstNode) -> Result<Type> {
        let s = Type::infer(node.clone(), &self.type_registry)?;
        match s {
            Type::Unknown => match node {
                AstNode::Ident(name, loc) => {
                    let var = self
                        .scope_manager
                        .lookup(name)
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
                    Ok(var.ty.clone())
                }
                AstNode::Call(name, args, _) => {
                    if let Some((_, _, _, return_type)) = self.native_registry.get(name) {
                        if name == "box" && !args.is_empty() {
                            let arg_type = self.infer_type(&args[0])?;
                            return Ok(Type::Box(Box::new(arg_type)));
                        }

                        return Ok(return_type.clone());
                    }

                    if let Some(symbol) = self.symbol_registry.get(name) {
                        Ok(symbol.return_type.clone())
                    } else {
                        Ok(Type::Unknown)
                    }
                }
                AstNode::Ref(inner, mutable, _) => {
                    let inner_type = self.infer_type(inner)?;
                    Ok(Type::Reference(
                        Box::new(inner_type),
                        if *mutable {
                            Mutability::Mutable
                        } else {
                            Mutability::Immutable
                        },
                    ))
                }
                AstNode::Deref(inner, _) => {
                    let inner_type = self.infer_type(inner)?;
                    match inner_type {
                        Type::Reference(t, _) => Ok(*t),
                        Type::Box(t) => Ok(*t),
                        _ => Err(anyhow::anyhow!("Cannot dereference non-reference type")),
                    }
                }
                _ => Ok(Type::Unknown),
            },
            Type::Reference(inner_type, mutability) if *inner_type == Type::Unknown => {
                if let AstNode::Ref(inner, _, _) = node {
                    let inner_type = self.infer_type(inner)?;
                    Ok(Type::Reference(Box::new(inner_type), mutability))
                } else {
                    Ok(Type::Unknown)
                }
            }
            _ => Ok(s),
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
        let var = self
            .scope_manager
            .lookup(ident)
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
                        Source::from(fs::read_to_string(loc.0.clone()).unwrap()),
                    ))
                    .unwrap();
                anyhow::anyhow!("Varaible {ident:?} not found")
            })?
            .clone();

        // TODO: Fix when I add traits
        let is_copy_type = matches!(var.ty, Type::Int | Type::Bool | Type::Reference(_, _));

        if !is_copy_type {
            self.borrow_checker
                .mark_moved(ident.to_string(), loc.clone())?;
        }

        self.emit_opcode(Opcode::LoadLocal);
        self.emit_u16(var.local_idx);
        self.push_stack();
        Ok(var.ty)
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
        let dt = if let Some(data_type) = data_type.clone() {
            Type::from_string(data_type.0, &self.type_registry)?
        } else {
            self.infer_type(&expr)?
        };

        let var = Variable {
            ty: dt.clone(),
            local_idx: self.next_local,
            mutable: mutability,
            definition_loc: loc.clone(),
        };
        self.next_local += 1;

        self.scope_manager.define(name.to_string(), var.clone())?;

        let actual_type = self.compile_node(expr.clone())?;
        if !actual_type.can_convert_to(dt.clone()) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let mut builder = Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Unable to convert from {actual_type:?} to {:?}",
                    dt.clone()
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
                                Type::from_string(data_type.0.clone(), &self.type_registry)?
                            ))
                            .with_color(b),
                    )
                    .with_help(format!(
                        "Remove the type specifier or replace it with '{:?}'",
                        Type::from_string(data_type.0, &self.type_registry)?
                    ));
            }

            builder
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Unable to convert from {actual_type:?} to {dt:?}");
        }

        self.emit_opcode(Opcode::StoreLocal);
        self.emit_u16(var.local_idx);

        self.pop_stack();
        Ok(Type::Unit)
    }

    fn compile_assign(&mut self, target: AstNode, expr: AstNode, loc: Loc) -> Result<Type> {
        match target {
            AstNode::Ident(n, ident_loc) => {
                self.borrow_checker.can_use(&n, ident_loc.clone())?;

                let name = &n;
                let var = self
                    .scope_manager
                    .lookup(name)
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
                if !actual_type.can_convert_to(var.ty.clone()) {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Unable to convert from {actual_type:?} to {:?}",
                            var.ty
                        ))
                        .with_label(
                            Label::new(var.definition_loc.clone())
                                .with_message(format!("Expected type {:?}", var.ty))
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
                    bail!("Unable to convert from {actual_type:?} to {:?}", var.ty);
                }

                if !var.mutable {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!("Variable {name} is immutable"))
                        .with_label(
                            Label::new(var.definition_loc)
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
                self.emit_u16(var.local_idx);

                self.pop_stack();
                Ok(Type::Unit)
            }
            AstNode::Deref(node, loc) => {
                let node_loc = node.loc();
                let actual_type = self.compile_node(expr.clone())?;
                let expr_type = self.compile_node(*node.clone())?;
                match expr_type.clone() {
                    Type::Reference(inner, mutable) => match mutable {
                        Mutability::Mutable => {
                            if let AstNode::Ident(var_name, _) = *node {
                                self.borrow_checker
                                    .can_mutate_through_ref(&var_name, loc.clone())?;
                            }

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
                    Type::Box(inner) => {
                        if let AstNode::Ident(var_name, _) = *node {
                            self.borrow_checker
                                .can_mutate_through_ref(&var_name, loc.clone())?;
                        }

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
                        self.emit_opcode(Opcode::HeapStore);
                        Ok(Type::Unit)
                    }
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
            AstNode::FieldAccess(object, field_name, field_loc) => {
                let object_type = self.compile_node(*object.clone())?;

                let actual_type = if let Type::Reference(inner, mutability) = &object_type {
                    if !matches!(mutability, Mutability::Mutable) {
                        self.report_error(
                            &field_loc,
                            "Cannot mutate through immutable reference".to_string(),
                        );
                        bail!("Immutable reference");
                    }

                    inner.as_ref().clone()
                } else if let Type::Box(inner) = &object_type {
                    inner.as_ref().clone()
                } else {
                    object_type
                };

                if let Type::Struct(struct_id) = actual_type {
                    let struct_def = self
                        .type_registry
                        .get_struct_by_id(struct_id)
                        .ok_or_else(|| anyhow::anyhow!("Struct not found"))?
                        .clone();

                    let field_index = struct_def
                        .field_offset(&field_name)
                        .ok_or_else(|| anyhow::anyhow!("Field not found"))?;

                    let field_type = struct_def.fields[field_index as usize].ty.clone();

                    let value_type = self.compile_node(expr)?;

                    if !value_type.can_convert_to(field_type.clone()) {
                        self.report_error(
                            &loc,
                            format!(
                                "Type mismatch: cannot assign {value_type:?} to field of type {field_type:?}"
                            ),
                        );
                        bail!("Type mismatch");
                    }

                    self.emit_opcode(Opcode::FieldSet);
                    self.emit_u16(field_index);

                    self.pop_stack();
                    self.pop_stack();

                    if let AstNode::Ident(name, ident_loc) = *object {
                        self.push_stack();

                        let name = &name;
                        let var = self
                            .scope_manager
                            .lookup(name)
                            .ok_or_else(|| {
                                let mut colors = ColorGenerator::new();
                                let a = colors.next();
                                Report::build(ReportKind::Error, ident_loc.clone())
                                    .with_message(format!("Variable {name:?} not found"))
                                    .with_label(
                                        Label::new(ident_loc.clone())
                                            .with_message(format!(
                                                "Could not find a variable named {name:?}"
                                            ))
                                            .with_color(a),
                                    )
                                    .finish()
                                    .print((
                                        ident_loc.0.clone(),
                                        Source::from(
                                            fs::read_to_string(ident_loc.0.clone()).unwrap(),
                                        ),
                                    ))
                                    .unwrap();
                                anyhow::anyhow!("Varaible {name:?} not found")
                            })?
                            .clone();

                        if !Type::Struct(struct_def.id).can_convert_to(var.ty.clone()) {
                            let mut colors = ColorGenerator::new();
                            let a = colors.next();
                            let b = colors.next();
                            Report::build(ReportKind::Error, ident_loc.clone())
                                .with_message(format!(
                                    "Unable to convert from {:?} to {:?}",
                                    Type::Struct(struct_def.id),
                                    var.ty
                                ))
                                .with_label(
                                    Label::new(var.definition_loc.clone())
                                        .with_message(format!("Expected type {:?}", var.ty))
                                        .with_color(b),
                                )
                                .with_label(
                                    Label::new(loc.clone())
                                        .with_message(format!(
                                            "Expression has type {:?}",
                                            Type::Struct(struct_def.id)
                                        ))
                                        .with_color(a),
                                )
                                .finish()
                                .print((
                                    ident_loc.0.clone(),
                                    Source::from(fs::read_to_string(ident_loc.0).unwrap()),
                                ))
                                .unwrap();
                            bail!(
                                "Unable to convert from {:?} to {:?}",
                                Type::Struct(struct_def.id),
                                var.ty
                            );
                        }

                        if !var.mutable {
                            let mut colors = ColorGenerator::new();
                            let a = colors.next();
                            let b = colors.next();
                            Report::build(ReportKind::Error, ident_loc.clone())
                                .with_message(format!("Variable {name} is immutable"))
                                .with_label(
                                    Label::new(var.definition_loc)
                                        .with_message("Variable was not defined as mutable")
                                        .with_color(b),
                                )
                                .with_label(
                                    Label::new(ident_loc.clone())
                                        .with_message(
                                            "Variable must be mutable to allow assignment",
                                        )
                                        .with_color(a),
                                )
                                .finish()
                                .print((
                                    ident_loc.0.clone(),
                                    Source::from(fs::read_to_string(ident_loc.0).unwrap()),
                                ))
                                .unwrap();
                            bail!("Variable {name} is immutable");
                        }

                        self.emit_opcode(Opcode::StoreLocal);
                        self.emit_u16(var.local_idx);

                        self.pop_stack();
                    }

                    Ok(Type::Unit)
                } else {
                    self.report_error(
                        &field_loc,
                        "Cannot assign to field of non-struct type".to_string(),
                    );
                    bail!("Not a struct");
                }
            }
            _ => {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Assignment is only possible to an Ident, Reference or a Struct's field, got: {target:?}"
                    ))
                    .with_label(
                        Label::new(target.loc())
                            .with_message("Node is of type: {name:?}")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!(
                    "Assignment is only possible to an Ident, Reference or a Struct's field, got: {target:?}"
                );
            }
        }
    }

    fn compile_ref(&mut self, expr: AstNode, mutable: bool, loc: Loc) -> Result<Type> {
        match expr.clone() {
            AstNode::Ident(name, ident_loc) => {
                let var = self
                    .scope_manager
                    .lookup(&name)
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

                if mutable && !var.mutable {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Cannot take mutable reference to immutable variable {name}"
                        ))
                        .with_label(
                            Label::new(var.definition_loc.clone())
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

                let mutability = if mutable {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };

                self.borrow_checker
                    .can_borrow(&name, mutability.clone(), loc.clone())?;
                self.borrow_checker
                    .add_borrow(name.clone(), mutability, loc.clone());

                self.emit_opcode(Opcode::LoadRef);
                self.emit_u16(var.local_idx);
                self.emit_byte(if mutable { 1 } else { 0 });
                self.push_stack();

                Ok(Type::Reference(
                    Box::new(var.ty.clone()),
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
            Type::Box(inner) => {
                self.emit_opcode(Opcode::HeapLoad);
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

            self.scope_manager.enter_scope();
            self.borrow_checker.enter_scope();

            for node in branch.1.clone() {
                self.compile_node(node)?;
            }

            self.borrow_checker.exit_scope();
            self.scope_manager.exit_scope();

            self.emit_opcode(Opcode::Jump);
            write_end_to.push(self.current_function.as_ref().unwrap().code.len());
            self.emit_u32(u32::MAX);
        }

        let mut addr_to_write = (self.current_function.as_ref().unwrap().code.len()).to_le_bytes();
        let offset = *write_start_to.last().unwrap();
        self.current_function.as_mut().unwrap().code[offset..(4 + offset)]
            .copy_from_slice(&addr_to_write[..4]);

        if !unconditional.is_empty() {
            self.scope_manager.enter_scope();
            self.borrow_checker.enter_scope();

            for node in unconditional {
                self.compile_node(node)?;
            }

            self.borrow_checker.exit_scope();
            self.scope_manager.exit_scope();

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

        self.scope_manager.enter_scope();
        self.borrow_checker.enter_scope();

        for n in body {
            self.compile_node(n)?;
        }

        self.borrow_checker.exit_scope();
        self.scope_manager.exit_scope();

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
        self.scope_manager.reset_to_root();
        self.borrow_checker.reset();
        self.next_local = 0;

        for arg in args {
            let idx = self.next_local;
            let var = Variable {
                ty: Type::from_string(arg.1, &self.type_registry)?,
                local_idx: idx,
                mutable: false,
                definition_loc: arg.2,
            };
            self.scope_manager.define(arg.0, var)?;
            self.next_local += 1;
        }

        for node in body {
            self.compile_node(node)?;
        }

        Ok(Type::Unit)
    }

    fn compile_struct_def(
        &mut self,
        name: String,
        type_params: Vec<String>,
        field_defs: Vec<(String, String, Loc)>,
        loc: Loc,
    ) -> Result<Type> {
        let mut fields = Vec::new();

        for (i, (field_name, field_type_str, field_loc)) in field_defs.into_iter().enumerate() {
            let field_type = Type::from_string(field_type_str, &self.type_registry)?;
            fields.push(Field {
                name: field_name,
                ty: field_type,
                offset: i as u16,
                loc: field_loc,
            });
        }

        let struct_def = StructDef {
            id: 0, // Will be set by register_struct
            name: name.clone(),
            fields,
            type_params: type_params.clone(),
            methods: HashMap::new(),
            is_generic: !type_params.is_empty(),
            loc,
        };

        self.type_registry.register_struct(name, struct_def);
        Ok(Type::Unit)
    }

    fn compile_struct_literal(
        &mut self,
        type_name: String,
        field_values: Vec<(String, Box<AstNode>)>,
        loc: Loc,
    ) -> Result<Type> {
        let struct_def = self
            .type_registry
            .get_struct(&type_name)
            .ok_or_else(|| {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!("Struct {type_name:?} not found"))
                    .with_label(
                        Label::new(loc.clone())
                            .with_message("Unknown struct type")
                            .with_color(a),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(&loc.0).unwrap()),
                    ))
                    .unwrap();
                anyhow::anyhow!("Struct {type_name:?} not found")
            })?
            .clone();

        if field_values.len() != struct_def.fields.len() {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            Report::build(ReportKind::Error, loc.clone())
                .with_message(format!(
                    "Struct {type_name} has {} fields, but {} were provided",
                    struct_def.fields.len(),
                    field_values.len()
                ))
                .with_label(
                    Label::new(loc.clone())
                        .with_message("Incorrect number of fields")
                        .with_color(a),
                )
                .finish()
                .print((
                    loc.0.clone(),
                    Source::from(fs::read_to_string(&loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Incorrect number of struct fields");
        }

        for field_def in &struct_def.fields {
            let field_value = field_values
                .iter()
                .find(|(name, _)| name == &field_def.name)
                .ok_or_else(|| {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    Report::build(ReportKind::Error, loc.clone())
                        .with_message(format!(
                            "Missing field '{}' in struct literal",
                            field_def.name
                        ))
                        .with_label(
                            Label::new(loc.clone())
                                .with_message(format!("Field '{}' not provided", field_def.name))
                                .with_color(a),
                        )
                        .with_label(
                            Label::new(field_def.loc.clone())
                                .with_message("Field defined here")
                                .with_color(colors.next()),
                        )
                        .finish()
                        .print((
                            loc.0.clone(),
                            Source::from(fs::read_to_string(&loc.0).unwrap()),
                        ))
                        .unwrap();
                    anyhow::anyhow!("Missing field in struct literal")
                })?;

            let actual_type = self.compile_node(*field_value.1.clone())?;

            if !actual_type.can_convert_to(field_def.ty.clone()) {
                let mut colors = ColorGenerator::new();
                let a = colors.next();
                let b = colors.next();
                Report::build(ReportKind::Error, loc.clone())
                    .with_message(format!(
                        "Type mismatch for field '{}': expected {:?}, got {:?}",
                        field_def.name, field_def.ty, actual_type
                    ))
                    .with_label(
                        Label::new(field_value.1.loc())
                            .with_message(format!("Expression has type {actual_type:?}"))
                            .with_color(a),
                    )
                    .with_label(
                        Label::new(field_def.loc.clone())
                            .with_message(format!("Field expects type {:?}", field_def.ty))
                            .with_color(b),
                    )
                    .finish()
                    .print((
                        loc.0.clone(),
                        Source::from(fs::read_to_string(&loc.0).unwrap()),
                    ))
                    .unwrap();
                bail!("Type mismatch in struct literal");
            }
        }

        self.emit_opcode(Opcode::StructNew);
        self.emit_u32(struct_def.id);
        self.emit_u16(struct_def.fields.len() as u16);

        Ok(Type::Struct(struct_def.id))
    }

    fn compile_field_access(&mut self, struc: AstNode, field: String, loc: Loc) -> Result<Type> {
        let struct_type = self.compile_node(struc)?;

        let actual_type = if let Type::Reference(inner, _) = &struct_type {
            self.emit_opcode(Opcode::LoadLocal);
            inner.as_ref().clone()
        } else {
            struct_type
        };

        match actual_type {
            Type::Struct(id) => {
                let struct_def = self
                    .type_registry
                    .get_struct_by_id(id)
                    .ok_or_else(|| anyhow::anyhow!("Struct not found"))?;
                let field_index = struct_def.field_offset(&field).ok_or_else(|| {
                    self.report_error(
                        &loc,
                        format!(
                            "Field '{}' not found in struct '{}'",
                            field, struct_def.name
                        ),
                    );
                    anyhow::anyhow!("Field not found")
                })?;

                let field_type = struct_def.fields[field_index as usize].ty.clone();

                self.emit_opcode(Opcode::FieldGet);
                self.emit_u16(field_index);

                Ok(field_type)
            }
            _ => {
                self.report_error(&loc, format!("Cannot access field on type {actual_type:?}"));
                bail!("Not a struct");
            }
        }
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

            let mut created_borrows = Vec::new();

            for (i, arg) in args.iter().enumerate() {
                if let AstNode::Ref(expr, is_mutable, _) = arg
                    && let AstNode::Ident(var_name, _) = expr.as_ref()
                {
                    let mutability = if *is_mutable {
                        Mutability::Mutable
                    } else {
                        Mutability::Immutable
                    };

                    created_borrows.push((var_name.clone(), mutability));
                }

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

            for (var_name, _) in created_borrows {
                self.borrow_checker.release_borrows(&var_name);
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

        let mut created_borrows = Vec::new();

        for arg in args.iter() {
            if let AstNode::Ref(expr, is_mutable, _) = arg
                && let AstNode::Ident(var_name, _) = expr.as_ref()
            {
                let mutability = if *is_mutable {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };
                created_borrows.push((var_name.clone(), mutability));
            }

            self.compile_node(arg.clone())?;
            self.pop_stack();
        }

        self.emit_opcode(Opcode::CallNative);
        self.emit_u32(name_idx);
        self.emit_byte(args.len() as u8);

        if !matches!(return_type, Type::Unit) {
            self.push_stack();
        }

        for (var_name, _) in created_borrows {
            self.borrow_checker.release_borrows(&var_name);
        }

        Ok(return_type)
    }

    fn add_constant(&mut self, constant: Constant) -> u32 {
        if let Some(index) = self.bytecode.const_pool.iter().position(|c| c == &constant) {
            return index as u32;
        }
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

    fn report_error(&self, loc: &Loc, message: String) {
        use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
        use std::fs;

        let mut colors = ColorGenerator::new();
        let a = colors.next();
        Report::build(ReportKind::Error, loc.clone())
            .with_message(message.clone())
            .with_label(Label::new(loc.clone()).with_message(message).with_color(a))
            .finish()
            .print((
                loc.0.clone(),
                Source::from(fs::read_to_string(&loc.0).unwrap_or_default()),
            ))
            .ok();
    }
}
