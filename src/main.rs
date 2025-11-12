use std::{
    fs::{self, File},
    path::PathBuf,
};

use anyhow::{Ok, Result};
use clap::Parser;

use crate::{bytecode::BytecodeFile, vm::VM};

pub mod bytecode;
pub mod compiler;
pub mod native;
pub mod parser;
pub mod registry;
pub mod vm;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct RoccaVM {
    file: PathBuf,

    /// Only compile to bytecode
    #[arg(short, long)]
    compile: bool,

    /// Run from compiled bytecode
    #[arg(short, long)]
    run: bool,
}

fn main() -> Result<()> {
    let cli = RoccaVM::parse();

    if cli.run {
        let mut file = File::open(cli.file)?;
        let bytecode = BytecodeFile::read(&mut file)?;

        let mut vm = VM::new(bytecode);
        vm.run()?;

        return Ok(());
    }

    let contents = fs::read_to_string(cli.file.clone())?;

    let tree = parser::parse(contents.as_str())?;

    let mut compiler = compiler::Compiler::default();
    let bytecode = compiler.compile(tree)?;

    if cli.compile {
        let mut out_name = cli.file.clone();
        out_name.set_extension("rcb");
        let mut file = File::create(out_name)?;
        bytecode.write(&mut file)?;
        return Ok(());
    }

    let mut vm = VM::new(bytecode);
    vm.run()?;

    Ok(())
}
