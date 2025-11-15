use anyhow::{Result, bail};
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
    String(String),
    Ident(String),
    BinaryOp(Box<AstNode>, String, Box<AstNode>),
    UnaryOp(Box<AstNode>, String),
    Comparison(Box<AstNode>, String, Box<AstNode>),
    Let(String, Box<AstNode>),
    Assign(String, Box<AstNode>),
    Return(Option<Box<AstNode>>),
    Call(String, Vec<AstNode>),
    FnDef(String, Vec<String>, Vec<AstNode>),
    If(Vec<(Box<AstNode>, Vec<AstNode>)>, Vec<AstNode>),
    While(Box<AstNode>, Vec<AstNode>),
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
        Rule::string => Ok(AstNode::String(unescape_string(
            pair.as_str().trim_matches('"'),
        )?)),
        Rule::logic => {
            let mut pairs = pair.into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap())?;

            while let Some(op) = pairs.next() {
                let op = op.as_str().trim().to_string();
                let right = build_ast(pairs.next().unwrap())?;

                left = AstNode::BinaryOp(Box::new(left), op, Box::new(right))
            }

            Ok(left)
        }
        Rule::comparison => {
            let mut pairs = pair.into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let left = build_ast(pairs.next().unwrap())?;

            let first_pair = match pairs.next() {
                Some(p) => p,
                None => return Ok(left),
            };

            let current_op = first_pair.as_str().trim().to_string();
            let mut current_right = build_ast(pairs.next().unwrap())?;

            let mut final_cmp = AstNode::Comparison(
                Box::new(left.clone()),
                current_op,
                Box::new(current_right.clone()),
            );

            while let Some(op) = pairs.next() {
                let next_left = current_right;
                let next_op = op.as_str().trim().to_string();
                let next_right = build_ast(pairs.next().unwrap())?;

                let next_cmp =
                    AstNode::Comparison(Box::new(next_left), next_op, Box::new(next_right.clone()));

                final_cmp =
                    AstNode::BinaryOp(Box::new(final_cmp), "&&".to_string(), Box::new(next_cmp));

                current_right = next_right;
            }

            Ok(final_cmp)
        }
        Rule::expr => {
            let mut pairs = pair.into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap())?;

            while let Some(op) = pairs.next() {
                let op = match op.as_rule() {
                    Rule::PLUS => "+",
                    Rule::MINUS => "-",
                    _ => bail!("Unexpected operator: {op:?}"),
                };
                let right = build_ast(pairs.next().unwrap())?;

                left = AstNode::BinaryOp(Box::new(left), op.to_string(), Box::new(right));
            }

            Ok(left)
        }
        Rule::term => {
            let mut pairs = pair.into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap())?;

            while let Some(op) = pairs.next() {
                let op = match op.as_rule() {
                    Rule::STAR => "*",
                    Rule::SLASH => "/",
                    Rule::PERCENT => "%",
                    _ => bail!("Unexpected operator: {op:?}"),
                };
                let right = build_ast(pairs.next().unwrap())?;

                left = AstNode::BinaryOp(Box::new(left), op.to_string(), Box::new(right));
            }

            Ok(left)
        }
        Rule::factor => {
            let mut pairs = pair.into_inner();
            let first = pairs.next().expect("Need at least one pair");

            match first.as_rule() {
                Rule::MINUS | Rule::BANG => Ok(AstNode::UnaryOp(
                    Box::new(build_ast(
                        pairs.next().expect("Expected primary after factor"),
                    )?),
                    first.as_str().trim().to_string(),
                )),
                Rule::primary => build_ast(first),
                _ => Err(anyhow::anyhow!("Unexpected rule: {:?}", first.as_rule())),
            }
        }
        Rule::primary => build_ast(pair.into_inner().next().unwrap()),
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
        Rule::if_stmt => {
            let mut pairs = pair.into_inner();
            let condition = build_ast(pairs.next().expect("If statement must have condition"))?;

            let mut cond_pairs = Vec::new();
            cond_pairs.push((Box::new(condition), Vec::new()));
            let mut uncond_stmts = Vec::new();
            for p in pairs {
                match p.as_rule() {
                    Rule::else_if_stmt => {
                        let mut pairs = p.into_inner();
                        let condition = build_ast(
                            pairs.next().expect("If-Else statement must have condition"),
                        )?;
                        cond_pairs.push((Box::new(condition), Vec::new()));

                        for p in pairs {
                            cond_pairs.last_mut().unwrap().1.push(build_ast(p)?);
                        }
                    }
                    Rule::else_stmt => {
                        for s in p.into_inner() {
                            uncond_stmts.push(build_ast(s)?);
                        }
                    }
                    _ => cond_pairs.last_mut().unwrap().1.push(build_ast(p)?),
                }
            }

            Ok(AstNode::If(cond_pairs, uncond_stmts))
        }
        Rule::while_loop => {
            let mut pairs = pair.into_inner();
            let condition = build_ast(pairs.next().expect("While loop must have condition"))?;

            Ok(AstNode::While(
                Box::new(condition),
                pairs.map(|p| build_ast(p).unwrap()).collect(),
            ))
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
        _ => Err(anyhow::anyhow!("Unexpected rule: {:?}", pair.as_rule())),
    }
}

fn unescape_string(input: &str) -> Result<String> {
    let mut output = String::with_capacity(input.len());
    let mut chars = input.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\\' {
            match chars.next() {
                Some('n') => output.push('\n'),
                Some('r') => output.push('\r'),
                Some('t') => output.push('\t'),
                Some('b') => output.push('\u{0008}'),
                Some('f') => output.push('\u{000C}'),
                Some('"') => output.push('"'),
                Some('\\') => output.push('\\'),
                Some('/') => output.push('/'),

                Some('u') => {
                    let hex_chars: String = chars.by_ref().take(4).collect();
                    if hex_chars.len() == 4 {
                        match u16::from_str_radix(&hex_chars, 16) {
                            Ok(code) => match char::from_u32(code as u32) {
                                Some(uni_char) => output.push(uni_char),
                                None => bail!("Invalid Unicode codepoint in \\uXXXX escape"),
                            },
                            Err(_) => bail!("Invalid hexadecimal in \\uXXXX escape"),
                        }
                    } else {
                        bail!("Incomplete \\uXXXX escape sequence");
                    }
                }

                Some(other) => {
                    output.push('\\');
                    output.push(other);
                }
                None => {
                    output.push('\\');
                    break;
                }
            }
        } else {
            output.push(c);
        }
    }

    Ok(output)
}
