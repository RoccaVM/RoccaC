use std::{
    fs::{self, File},
    path::PathBuf,
};

use anyhow::{Ok, Result};
use clap::Parser;

use crate::{bytecode::BytecodeFile, vm::VM};

pub mod borrow_checker;
pub mod bytecode;
pub mod compiler;
pub mod disassembler;
pub mod heap;
pub mod native;
pub mod parser;
pub mod registry;
pub mod scope;
pub mod types;
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

    /// Add debug symbols
    #[arg(short, long)]
    debug: bool,

    /// Show disassembled bytecode
    #[arg(long)]
    disasm: bool,
}

fn main() -> Result<()> {
    let cli = RoccaVM::parse();

    if cli.disasm {
        let mut file = File::open(cli.file)?;
        let bytecode = BytecodeFile::read(&mut file)?;
        return disassembler::ui::run(bytecode);
    }

    if cli.run {
        let mut file = File::open(cli.file)?;
        let bytecode = BytecodeFile::read(&mut file)?;

        let mut vm = VM::new(bytecode);
        vm.run()?;

        return Ok(());
    }

    let contents = fs::read_to_string(cli.file.clone())?;

    let tree = parser::parse(contents.as_str(), cli.file.to_str().unwrap())?;

    //println!("{tree:#?}");

    let mut compiler = compiler::Compiler::default();
    let mut bytecode = compiler.compile(tree)?;
    bytecode.header.flags = bytecode.header.flags.with_debug_symbols(cli.debug);

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
