use std::collections::HashMap;

use anyhow::{Ok, Result};

use crate::{
    parser::{AstNode, Loc},
    types::{Type, TypeRegistry},
};

pub struct SymbolRegistry {
    functions: HashMap<String, FunctionSymbol>,

    current_fn_index: u32,
}

#[derive(Clone, Debug)]
pub struct FunctionSymbol {
    pub name: String,
    pub return_type: Type,
    pub arity: u8,
    pub arg_types: Vec<(Type, Loc)>,
    pub returns: bool,
    pub index: u32,
    pub loc: Loc,
}

impl Default for SymbolRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolRegistry {
    pub fn new() -> Self {
        Self {
            functions: HashMap::new(),

            current_fn_index: 0,
        }
    }

    pub fn traverse(&mut self, node: AstNode, registry: &TypeRegistry) -> Result<()> {
        match node {
            AstNode::FnDef(name, args, return_type, body, loc) => {
                let mut ret = -1;
                for n in body {
                    let found = find_return(n);
                    if found != -1 {
                        ret = found;
                        break;
                    }
                }

                let rt = if let Some(return_type) = return_type {
                    Type::from_string(return_type, registry)?
                } else {
                    Type::Unit
                };

                self.functions.insert(
                    name.clone(),
                    FunctionSymbol {
                        name,
                        return_type: rt,
                        arity: args.len() as u8,
                        arg_types: args
                            .into_iter()
                            .map(|a| Type::from_string(a.1, registry).map(|t| (t, a.2)))
                            .collect::<Result<Vec<(Type, Loc)>, anyhow::Error>>()?,
                        returns: ret == 1,
                        index: self.current_fn_index,
                        loc,
                    },
                );

                self.current_fn_index += 1;

                Ok(())
            }
            _ => Ok(()),
        }
    }

    pub fn get(&self, name: &str) -> Option<&FunctionSymbol> {
        self.functions.get(name)
    }
}

// Find nested return statements, returns as follows
// -1 - none found
// 0  - found, no value
// 1  - found, returns value
fn find_return(node: AstNode) -> i8 {
    match node {
        AstNode::Return(v, _loc) => {
            if v.is_some() {
                1
            } else {
                0
            }
        }
        AstNode::FnDef(_, _, _, body, _loc) => {
            for n in body {
                let found = find_return(n);
                if found != -1 {
                    return found;
                }
            }
            -1
        }
        _ => -1,
    }
}
