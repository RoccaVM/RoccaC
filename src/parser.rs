use anyhow::{Ok, Result, bail};
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
    Assign(String, Box<AstNode>),
    Return(Option<Box<AstNode>>),
    Call(String, Vec<AstNode>),
    FnDef(String, Vec<String>, Vec<AstNode>),
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
                if !matches!(op.as_rule(), Rule::op) {
                    bail!("Expected op, got: {op:?}");
                }
                let op = op.as_str().trim();
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
        Rule::assign_stmt => {
            let mut pairs = pair.into_inner();
            if pairs.len() != 2 {
                return Err(ParserError::WrongPairCount(2, pairs.len()).into());
            }

            let name = pairs.next().unwrap().as_str().trim().to_string();
            let expr = build_ast(pairs.next().unwrap())?;
            Ok(AstNode::Assign(name, Box::new(expr)))
        }
        Rule::return_stmt => {
            let mut pairs = pair.into_inner();
            if pairs.len() > 1 {
                return Err(ParserError::WrongPairCount(1, pairs.len()).into());
            }

            if pairs.len() == 0 {
                Ok(AstNode::Return(None))
            } else {
                let expr = build_ast(pairs.next().unwrap())?;
                Ok(AstNode::Return(Some(Box::new(expr))))
            }
        }
        Rule::call => {
            let mut pairs = pair.into_inner();

            let name = pairs
                .next()
                .expect("Must specify name of function to call")
                .as_str()
                .trim()
                .to_string();

            let mut args = Vec::with_capacity(pairs.len());

            for p in pairs {
                args.push(build_ast(p)?);
            }

            Ok(AstNode::Call(name, args))
        }
        Rule::fn_def => {
            let mut pairs = pair.into_inner();

            let name = pairs
                .next()
                .expect("Function definition must include name")
                .as_str()
                .trim()
                .to_string();

            let mut args = Vec::new();
            let mut body = Vec::new();
            for p in pairs {
                if matches!(p.as_rule(), Rule::ident) {
                    args.push(p.as_str().trim().to_string());
                } else if matches!(p.as_rule(), Rule::stmt) {
                    body.push(build_ast(p)?);
                } else {
                    bail!(
                        "Unexpected node, expected either ident or stmt, found: {:?}",
                        p.as_rule()
                    );
                }
            }

            Ok(AstNode::FnDef(name, args, body))
        }
        Rule::stmt => Ok(build_ast(pair.into_inner().next().unwrap())?),
        _ => {
            println!("{:?}", pair.as_rule());
            unreachable!();
        }
    }
}
