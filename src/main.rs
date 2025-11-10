use std::{fs, path::PathBuf};

use anyhow::Result;
use clap::Parser;

use crate::vm::VM;

pub mod bytecode;
pub mod compiler;
pub mod native;
pub mod parser;
pub mod vm;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct RoccaVM {
    file: PathBuf,
}

fn main() -> Result<()> {
    let cli = RoccaVM::parse();
    let contents = fs::read_to_string(cli.file)?;

    let tree = parser::parse(contents.as_str())?;
    println!("{tree:?}");

    let mut compiler = compiler::Compiler::default();
    let bytecode = compiler.compile(tree)?;

    //println!("{bytecode:#?}");

    let mut vm = VM::new(bytecode);
    vm.run()?;

    Ok(())
}
