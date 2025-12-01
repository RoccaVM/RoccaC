use std::collections::HashMap;

use anyhow::Result;

use crate::parser::AstNode;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Int,
    Bool,
    String,
    Unit,
    Struct(StructId),
    Enum(EnumId),
    Reference(Box<Type>, Mutability),
    Box(Box<Type>),
    Array(Box<Type>, Option<usize>),
    Generic(String),
    GenericInstance(StructId, Vec<Type>),
    Never,
    Unknown,
}

type StructId = u32;
type EnumId = u32;

#[derive(Clone, Debug, PartialEq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

impl Type {
    pub fn from_string(ts: String) -> Result<Self> {
        if ts.starts_with("&mut") {
            let inner = ts.strip_prefix("&mut").unwrap();
            return Ok(Self::Reference(
                Box::new(Self::from_string(inner.to_string())?),
                Mutability::Mutable,
            ));
        } else if ts.starts_with("&") {
            let inner = ts.strip_prefix("&").unwrap();
            return Ok(Self::Reference(
                Box::new(Self::from_string(inner.to_string())?),
                Mutability::Immutable,
            ));
        }

        if ts.starts_with("Box<") && ts.ends_with(">") {
            let inner = &ts[4..ts.len() - 1];
            return Ok(Self::Box(Box::new(Self::from_string(inner.to_string())?)));
        }

        match ts.trim() {
            "Int" => Ok(Self::Int),
            "Bool" => Ok(Self::Bool),
            "String" => Ok(Self::String),
            "Unit" => Ok(Self::Unit),
            "Never" | "!" => Ok(Self::Never),
            _ => Err(anyhow::anyhow!("Unable to convert '{ts}' to a type")),
        }
    }

    pub fn infer(ast: AstNode) -> Result<Self> {
        match ast {
            AstNode::Number(_, _) => Ok(Self::Int),
            AstNode::String(_, _) => Ok(Self::String),
            AstNode::Ref(inner, mutable, _) => {
                let inner_type = Self::infer(*inner)?;
                Ok(Self::Reference(
                    Box::new(inner_type),
                    if mutable {
                        Mutability::Mutable
                    } else {
                        Mutability::Immutable
                    },
                ))
            }
            AstNode::Deref(inner, _) => {
                let inner_type = Self::infer(*inner)?;
                match inner_type {
                    Type::Reference(t, _) => Ok(*t),
                    Type::Box(t) => Ok(*t),
                    _ => Err(anyhow::anyhow!("Cannot dereference non-reference type")),
                }
            }
            AstNode::BinaryOp(_, op, _, _) => match op.as_str() {
                "+" | "-" | "*" | "/" | "%" => Ok(Self::Int),
                "&&" | "||" => Ok(Self::Bool),
                _ => Ok(Self::Unknown),
            },
            AstNode::Comparison(_, _, _, _) => Ok(Self::Bool),
            AstNode::UnaryOp(_, op, _) => match op.as_str() {
                "-" => Ok(Self::Int),
                "!" => Ok(Self::Bool),
                _ => Ok(Self::Unknown),
            },
            _ => Ok(Self::Unknown),
        }
    }

    pub fn can_convert_to(&self, other: Self) -> bool {
        if *self == other {
            return true;
        }

        match (self, other) {
            (Type::Int, Type::Bool) => true,
            (Type::Bool, Type::Int) => true,
            (
                Type::Reference(inner1, Mutability::Mutable),
                Type::Reference(inner2, Mutability::Immutable),
            ) => inner1.can_convert_to(*inner2),
            (Type::Reference(inner1, m1), Type::Reference(inner2, m2)) => {
                *m1 == m2 && inner1.can_convert_to(*inner2)
            }
            (Type::Box(inner1), Type::Box(inner2)) => *inner1 == inner2,
            (Type::Unknown, _) => true,
            (_, Type::Unknown) => true,
            _ => false,
        }
    }

    pub fn is_copy(&self) -> bool {
        match self {
            Type::Int | Type::Bool | Type::Unit => true,
            Type::Reference(_, _) => true,
            Type::Array(inner, _) => inner.is_copy(),
            _ => false,
        }
    }

    pub fn deref(&self) -> Option<&Type> {
        match self {
            Type::Reference(inner, _) => Some(inner),
            Type::Box(inner) => Some(inner),
            _ => None,
        }
    }

    pub fn unify(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Type::Unknown, t) | (t, Type::Unknown) => Some(t.clone()),
            (a, b) if a == b => Some(a.clone()),

            (Type::Reference(i1, m1), Type::Reference(i2, m2)) if m1 == m2 => i1
                .unify(i2)
                .map(|inner| Type::Reference(Box::new(inner), m1.clone())),

            (Type::Box(i1), Type::Box(i2)) => i1.unify(i2).map(|inner| Type::Box(Box::new(inner))),

            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub ty: Type,
    pub offset: u16,
}

#[derive(Clone, Debug)]
pub struct StructDef {
    pub name: String,
    pub fields: Vec<Field>,
    pub type_params: Vec<String>,
    pub methods: HashMap<String, u32>,
    pub is_generic: bool,
}

impl StructDef {
    pub fn field_offset(&self, field_name: &str) -> Option<u16> {
        self.fields
            .iter()
            .find(|f| f.name == field_name)
            .map(|f| f.offset)
    }

    pub fn field_type(&self, field_name: &str) -> Option<&Type> {
        self.fields
            .iter()
            .find(|f| f.name == field_name)
            .map(|f| &f.ty)
    }

    pub fn total_size(&self) -> u16 {
        self.fields.last().map(|f| f.offset + 1).unwrap_or(0)
    }
}
