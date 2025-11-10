use std::{fs, path::PathBuf};

use anyhow::Result;
use clap::Parser;

pub mod bytecode;
pub mod compiler;
pub mod parser;

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

    println!("{bytecode:#?}");

    Ok(())
}
