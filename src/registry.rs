use std::collections::HashMap;

use anyhow::{Ok, Result};

use crate::parser::AstNode;

pub struct SymbolRegistry {
    functions: HashMap<String, FunctionSymbol>,

    current_fn_index: u32,
}

#[derive(Clone, Debug)]
pub struct FunctionSymbol {
    pub name: String,
    pub arity: u8,
    pub returns: bool,
    pub index: u32,
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

    pub fn traverse(&mut self, node: AstNode) -> Result<()> {
        match node {
            AstNode::FnDef(name, args, body) => {
                let mut ret = -1;
                for n in body {
                    let found = find_return(n);
                    if found != -1 {
                        ret = found;
                        break;
                    }
                }

                self.functions.insert(
                    name.clone(),
                    FunctionSymbol {
                        name,
                        arity: args.len() as u8,
                        returns: ret == 1,
                        index: self.current_fn_index,
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
        AstNode::Return(v) => {
            if v.is_some() {
                1
            } else {
                0
            }
        }
        AstNode::FnDef(_, _, body) => {
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
