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
    Array(Box<Type>, Option<usize>),
    Generic(String),
    GenericInstance(StructId, Vec<Type>),
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

        match ts.trim() {
            "Int" => Ok(Self::Int),
            "Bool" => Ok(Self::Bool),
            "String" => Ok(Self::String),
            "Unit" => Ok(Self::Unit),
            _ => Err(anyhow::anyhow!("Unable to convert '{ts}' to a type")),
        }
    }

    pub fn infer(ast: AstNode) -> Result<Self> {
        match ast {
            AstNode::Number(_, _) => Ok(Self::Int),
            AstNode::String(_, _) => Ok(Self::String),
            _ => Err(anyhow::anyhow!("Unable to infer type: {ast:?}")),
        }
    }

    pub fn can_convert_to(&self, other: Self) -> bool {
        if *self == other {
            return true;
        }

        match self {
            Type::Int => matches!(other, Type::Bool),
            Type::Bool => matches!(other, Type::Int),
            _ => false,
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
