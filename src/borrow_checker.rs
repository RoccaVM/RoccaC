use std::{collections::HashMap, fs};

use anyhow::{Result, bail};
use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};

use crate::{parser::Loc, types::Mutability};

#[derive(Clone, Debug)]
pub struct Borrow {
    pub variable: String,
    pub mutability: Mutability,
    pub location: Loc,
    pub scope_id: usize,
    pub borrow_id: usize,
}

#[derive(Clone, Debug)]
pub struct BorrowState {
    active_borrows: HashMap<String, Vec<Borrow>>,
    moved_variables: HashMap<String, Loc>,
}

impl Default for BorrowState {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowState {
    pub fn new() -> Self {
        Self {
            active_borrows: HashMap::new(),
            moved_variables: HashMap::new(),
        }
    }

    pub fn clone_for_branch(&self) -> Self {
        Self {
            active_borrows: self.active_borrows.clone(),
            moved_variables: self.moved_variables.clone(),
        }
    }
}

pub struct BorrowChecker {
    state_stack: Vec<BorrowState>,
    current_scope_id: usize,
    next_scope_id: usize,
    next_borrow_id: usize,
}

impl Default for BorrowChecker {
    fn default() -> Self {
        Self::new()
    }
}

impl BorrowChecker {
    pub fn new() -> Self {
        BorrowChecker {
            state_stack: vec![BorrowState::new()],
            current_scope_id: 0,
            next_scope_id: 1,
            next_borrow_id: 0,
        }
    }

    pub fn enter_scope(&mut self) {
        let new_state = self.current_state().clone_for_branch();
        self.state_stack.push(new_state);
        self.current_scope_id = self.next_scope_id;
        self.next_scope_id += 1;
    }

    pub fn exit_scope(&mut self) {
        if self.state_stack.len() > 1 {
            let scope_id = self.current_scope_id;
            for borrows in self.current_state_mut().active_borrows.values_mut() {
                borrows.retain(|b| b.scope_id != scope_id);
            }

            self.state_stack.pop();
            if self.current_scope_id > 0 {
                self.current_scope_id -= 1;
            }
        }
    }

    pub fn reset(&mut self) {
        self.state_stack.truncate(1);
        self.state_stack[0] = BorrowState::new();
        self.current_scope_id = 0;
        self.next_borrow_id = 0;
    }

    fn current_state(&self) -> &BorrowState {
        self.state_stack.last().expect("No borrow stack")
    }

    fn current_state_mut(&mut self) -> &mut BorrowState {
        self.state_stack.last_mut().expect("No borrow stack")
    }

    pub fn can_borrow(&self, variable: &str, mutability: Mutability, location: Loc) -> Result<()> {
        // Check if variable has been moved
        if let Some(moved_loc) = self.current_state().moved_variables.get(variable) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();
            Report::build(ReportKind::Error, location.clone())
                .with_message(format!("Cannot borrow {variable:?} - value has been moved"))
                .with_label(
                    Label::new(moved_loc.clone())
                        .with_message("Value moved here")
                        .with_color(b),
                )
                .with_label(
                    Label::new(location.clone())
                        .with_message("Attempting to borrow moved value here")
                        .with_color(a),
                )
                .with_help("Consider borrowing the value instead of moving it")
                .finish()
                .print((
                    location.0.clone(),
                    Source::from(fs::read_to_string(&location.0).unwrap()),
                ))
                .unwrap();
            bail!("Cannot borrow moved value");
        }

        let existing_borrows = self
            .current_state()
            .active_borrows
            .get(variable)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        if existing_borrows.is_empty() {
            return Ok(());
        }

        match mutability {
            Mutability::Mutable => {
                // Cannot take mutable borrow if ANY other borrow exists
                let mut colors = ColorGenerator::new();
                let a = colors.next();

                let mut builder = Report::build(ReportKind::Error, location.clone())
                    .with_message(format!(
                        "Cannot borrow {variable:?} as mutable because it is already borrowed"
                    ))
                    .with_label(
                        Label::new(location.clone())
                            .with_message("Mutable borrow occurs here")
                            .with_color(a),
                    );

                for (i, borrow) in existing_borrows.iter().enumerate() {
                    let color = colors.next();
                    let borrow_type = match borrow.mutability {
                        Mutability::Mutable => "mutable",
                        Mutability::Immutable => "immutable",
                    };
                    builder = builder.with_label(
                        Label::new(borrow.location.clone())
                            .with_message(format!("Previous {borrow_type} borrow occurs here"))
                            .with_color(color),
                    );

                    if i == 0 {
                        builder = builder
                            .with_help("Mutable references require exclusive access to the value");
                    }
                }

                builder
                    .finish()
                    .print((
                        location.0.clone(),
                        Source::from(fs::read_to_string(&location.0).unwrap()),
                    ))
                    .unwrap();

                bail!("Cannot borrow as mutable while other borrows exist");
            }
            Mutability::Immutable => {
                // Cannot take immutable borrow if a mutable borrow exists
                let mutable_borrows: Vec<_> = existing_borrows
                    .iter()
                    .filter(|b| matches!(b.mutability, Mutability::Mutable))
                    .collect();

                if !mutable_borrows.is_empty() {
                    let mut colors = ColorGenerator::new();
                    let a = colors.next();
                    let b = colors.next();

                    Report::build(ReportKind::Error, location.clone())
                        .with_message(format!(
                            "Cannot borrow {variable:?} as immutable because it is already borrowed as mutable"
                        ))
                        .with_label(
                            Label::new(location.clone())
                                .with_message("Immutable borrow occurs here")
                                .with_color(a),
                        )
                        .with_label(
                            Label::new(mutable_borrows[0].location.clone())
                                .with_message("Mutable borrow occurs here")
                                .with_color(b),
                        )
                        .with_help("Mutable borrows prevent any other borrows")
                        .finish()
                        .print((
                            location.0.clone(),
                            Source::from(fs::read_to_string(&location.0).unwrap()),
                        ))
                        .unwrap();

                    bail!("Cannot borrow as immutable while mutable borrow exists");
                }
                // Multiple immutable borrows are OK
            }
        }

        Ok(())
    }

    /// Register a new borrow and return its ID
    pub fn add_borrow(&mut self, variable: String, mutability: Mutability, location: Loc) -> usize {
        let borrow_id = self.next_borrow_id;
        self.next_borrow_id += 1;

        let borrow = Borrow {
            variable: variable.clone(),
            mutability,
            location,
            scope_id: self.current_scope_id,
            borrow_id,
        };

        self.current_state_mut()
            .active_borrows
            .entry(variable)
            .or_default()
            .push(borrow);

        borrow_id
    }

    /// Release a specific borrow by ID (for non-lexical lifetimes)
    pub fn release_borrow(&mut self, borrow_id: usize) {
        for borrows in self.current_state_mut().active_borrows.values_mut() {
            borrows.retain(|b| b.borrow_id != borrow_id);
        }

        // Clean up empty entries
        self.current_state_mut()
            .active_borrows
            .retain(|_, borrows| !borrows.is_empty());
    }

    /// Release all borrows of a variable in the current scope
    pub fn release_borrows(&mut self, variable: &str) {
        let current_scope_id = self.current_scope_id;
        if let Some(borrows) = self.current_state_mut().active_borrows.get_mut(variable) {
            borrows.retain(|b| b.scope_id != current_scope_id);
            if borrows.is_empty() {
                self.current_state_mut().active_borrows.remove(variable);
            }
        }
    }

    /// Check if we can use a variable (it hasn't been moved)
    pub fn can_use(&self, variable: &str, location: Loc) -> Result<()> {
        if let Some(moved_loc) = self.current_state().moved_variables.get(variable) {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();
            Report::build(ReportKind::Error, location.clone())
                .with_message(format!("Cannot use {variable:?} - value has been moved"))
                .with_label(
                    Label::new(moved_loc.clone())
                        .with_message("Value moved here")
                        .with_color(b),
                )
                .with_label(
                    Label::new(location.clone())
                        .with_message("Attempting to use moved value here")
                        .with_color(a),
                )
                .with_help("Consider cloning the value or using a reference")
                .finish()
                .print((
                    location.0.clone(),
                    Source::from(fs::read_to_string(&location.0).unwrap()),
                ))
                .unwrap();
            bail!("Cannot use moved value");
        }
        Ok(())
    }

    /// Check if we can mutate through a mutable reference
    pub fn can_mutate_through_ref(&self, variable: &str, location: Loc) -> Result<()> {
        // Check if there are any immutable borrows
        let existing_borrows = self
            .current_state()
            .active_borrows
            .get(variable)
            .map(|v| v.as_slice())
            .unwrap_or(&[]);

        let immutable_borrows: Vec<_> = existing_borrows
            .iter()
            .filter(|b| matches!(b.mutability, Mutability::Immutable))
            .collect();

        if !immutable_borrows.is_empty() {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();

            Report::build(ReportKind::Error, location.clone())
                .with_message(format!(
                    "Cannot mutate {variable:?} through mutable reference while immutable references exist"
                ))
                .with_label(
                    Label::new(location.clone())
                        .with_message("Mutation occurs here")
                        .with_color(a),
                )
                .with_label(
                    Label::new(immutable_borrows[0].location.clone())
                        .with_message("Immutable borrow prevents mutation")
                        .with_color(b),
                )
                .finish()
                .print((
                    location.0.clone(),
                    Source::from(fs::read_to_string(&location.0).unwrap()),
                ))
                .unwrap();

            bail!("Cannot mutate while immutable borrows exist");
        }

        Ok(())
    }

    /// Mark a variable as moved (for future use with heap types)
    pub fn mark_moved(&mut self, variable: String, location: Loc) -> Result<()> {
        // Check if there are any active borrows
        if let Some(borrows) = self.current_state().active_borrows.get(&variable)
            && !borrows.is_empty()
        {
            let mut colors = ColorGenerator::new();
            let a = colors.next();
            let b = colors.next();

            Report::build(ReportKind::Error, location.clone())
                .with_message(format!("Cannot move {variable:?} while borrowed"))
                .with_label(
                    Label::new(location.clone())
                        .with_message("Move occurs here")
                        .with_color(a),
                )
                .with_label(
                    Label::new(borrows[0].location.clone())
                        .with_message("Value is borrowed here")
                        .with_color(b),
                )
                .with_help("Consider cloning the value or ending the borrow")
                .finish()
                .print((
                    location.0.clone(),
                    Source::from(fs::read_to_string(&location.0).unwrap()),
                ))
                .unwrap();

            bail!("Cannot move borrowed value");
        }

        self.current_state_mut()
            .moved_variables
            .insert(variable, location);
        Ok(())
    }

    /// Get all active borrows (for debugging)
    pub fn active_borrows(&self) -> Vec<&Borrow> {
        self.current_state()
            .active_borrows
            .values()
            .flat_map(|v| v.iter())
            .collect()
    }
}
