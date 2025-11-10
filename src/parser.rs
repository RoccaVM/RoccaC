use anyhow::Result;
use pest::{Parser, iterators::Pair};
use pest_derive::Parser;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "syntax.pest"]
struct SyntaxParser;

#[derive(Error, Debug)]
pub enum ParserError {
    #[error("Wrong pair count: expected {0}, found {1}")]
    WrongPairCount(usize, usize),
}

#[derive(Clone, Debug)]
pub enum AstNode {
    Number(i64),
    Ident(String),
    BinaryOp(Box<AstNode>, String, Box<AstNode>),
    Let(String, Box<AstNode>),
    Print(Box<AstNode>),
}

pub fn parse(source: &str) -> Result<Vec<AstNode>> {
    let pairs = SyntaxParser::parse(Rule::prog, source)?;
    let mut ast = Vec::new();

    for pair in pairs {
        //pair_tree(pair, 0);
        ast.push(build_ast(pair)?);
    }

    Ok(ast)
}

fn build_ast(pair: Pair<Rule>) -> Result<AstNode> {
    match pair.as_rule() {
        Rule::number => Ok(AstNode::Number(pair.as_str().parse()?)),
        Rule::ident => Ok(AstNode::Ident(pair.as_str().trim().to_string())),
        Rule::expr => {
            let mut pairs = pair.into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap())?;

            while let Some(op) = pairs.next() {
                let op = match op.as_rule() {
                    Rule::add => "+",
                    Rule::sub => "-",
                    _ => unreachable!(),
                };
                let right = build_ast(pairs.next().unwrap())?;

                left = AstNode::BinaryOp(Box::new(left), op.to_string(), Box::new(right));
            }

            Ok(left)
        }
        Rule::let_stmt => {
            let mut pairs = pair.into_inner();
            if pairs.len() != 2 {
                return Err(ParserError::WrongPairCount(2, pairs.len()).into());
            }

            let name = pairs.next().unwrap().as_str().trim().to_string();
            let expr = build_ast(pairs.next().unwrap())?;
            Ok(AstNode::Let(name, Box::new(expr)))
        }
        Rule::print => {
            let mut pairs = pair.into_inner();
            if pairs.len() != 1 {
                return Err(ParserError::WrongPairCount(1, pairs.len()).into());
            }

            let expr = build_ast(pairs.next().unwrap())?;
            Ok(AstNode::Print(Box::new(expr)))
        }
        Rule::stmt => build_ast(pair),
        _ => {
            println!("{:?}", pair.as_rule());
            unreachable!();
        }
    }
}
