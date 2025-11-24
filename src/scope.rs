use std::{collections::HashMap, fs};

use anyhow::{Result, bail};
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

use crate::{parser::Loc, types::Type};

#[derive(Debug, Clone)]
pub struct Variable {
    pub ty: Type,
    pub local_idx: u16,
    pub mutable: bool,
    pub definition_loc: Loc,
}

#[derive(Debug, Clone)]
pub struct Scope {
    pub variables: HashMap<String, Variable>,
    pub parent: Option<usize>,
}

impl Scope {
    pub fn new(parent: Option<usize>) -> Self {
        Scope {
            variables: HashMap::new(),
            parent,
        }
    }
}

#[derive(Debug)]
pub struct ScopeManager {
    scopes: Vec<Scope>,
    current_scope: usize,
}

impl Default for ScopeManager {
    fn default() -> Self {
        Self::new()
    }
}

impl ScopeManager {
    pub fn new() -> Self {
        Self {
            scopes: vec![Scope::new(None)],
            current_scope: 0,
        }
    }

    pub fn enter_scope(&mut self) {
        let new_scope = Scope::new(Some(self.current_scope));
        self.scopes.push(new_scope);
        self.current_scope = self.scopes.len() - 1;
    }

    pub fn exit_scope(&mut self) {
        if let Some(parent) = self.scopes[self.current_scope].parent {
            self.current_scope = parent;
        }
    }

    pub fn define(&mut self, name: String, var: Variable) -> Result<()> {
        let scope = &mut self.scopes[self.current_scope];

        if let Some(def_var) = scope.variables.get(&name) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();
            Report::build(ReportKind::Error, var.definition_loc.clone())
                .with_message(format!("Variable {name} already defined in this scope"))
                .with_label(
                    Label::new(def_var.definition_loc.clone())
                        .with_message("Varaible already defined here")
                        .with_color(b),
                )
                .with_label(
                    Label::new(var.definition_loc.clone())
                        .with_message("Variable redefined here")
                        .with_color(a),
                )
                .with_help("Either mutate the first definition or rename the second one.")
                .finish()
                .print((
                    var.definition_loc.0.clone(),
                    Source::from(fs::read_to_string(var.definition_loc.0).unwrap()),
                ))
                .unwrap();
            bail!("Variable {name} already defined in this scope");
        }

        scope.variables.insert(name, var);
        Ok(())
    }

    pub fn lookup(&self, name: &str) -> Option<&Variable> {
        let mut current = self.current_scope;

        loop {
            let scope = &self.scopes[current];

            if let Some(var) = scope.variables.get(name) {
                return Some(var);
            }

            match scope.parent {
                Some(parent) => current = parent,
                None => return None,
            }
        }
    }

    pub fn exists_in_current_scope(&self, name: &str) -> bool {
        self.scopes[self.current_scope].variables.contains_key(name)
    }

    pub fn reset_to_root(&mut self) {
        self.scopes.truncate(1);
        self.current_scope = 0;
        self.scopes[0].variables.clear();
    }
}
