use std::ops::Range;

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

pub type Loc = (String, Range<usize>);

fn to_loc(file: &str, pair: Pair<Rule>) -> Loc {
    (
        file.to_string(),
        (pair.as_span().start())..(pair.as_span().end()),
    )
}

#[derive(Clone, Debug)]
pub enum AstNode {
    Number(i64, Loc),
    String(String, Loc),
    Ident(String, Loc),
    BinaryOp(Box<AstNode>, String, Box<AstNode>, Loc),
    UnaryOp(Box<AstNode>, String, Loc),
    Comparison(Box<AstNode>, String, Box<AstNode>, Loc),
    // Name, Mutable?, Optional data type and location, Assignment
    Let(String, bool, Option<(String, Loc)>, Box<AstNode>, Loc),
    Assign(Box<AstNode>, Box<AstNode>, Loc),
    Return(Option<Box<AstNode>>, Loc),
    Call(String, Vec<AstNode>, Loc),
    // Name, Argument[(Name, Data type)], Optional return type, Body
    FnDef(
        String,
        Vec<(String, String, Loc)>,
        Option<String>,
        Vec<AstNode>,
        Loc,
    ),
    If(Vec<(Box<AstNode>, Vec<AstNode>)>, Vec<AstNode>, Loc),
    While(Box<AstNode>, Vec<AstNode>, Loc),
    Ref(Box<AstNode>, bool, Loc),
    Deref(Box<AstNode>, Loc),
}

impl AstNode {
    pub fn loc(&self) -> Loc {
        match self {
            AstNode::Number(_, loc) => loc.clone(),
            AstNode::String(_, loc) => loc.clone(),
            AstNode::Ident(_, loc) => loc.clone(),
            AstNode::BinaryOp(_, _, _, loc) => loc.clone(),
            AstNode::UnaryOp(_, _, loc) => loc.clone(),
            AstNode::Comparison(_, _, _, loc) => loc.clone(),
            AstNode::Let(_, _, _, _, loc) => loc.clone(),
            AstNode::Assign(_, _, loc) => loc.clone(),
            AstNode::Return(_, loc) => loc.clone(),
            AstNode::Call(_, _, loc) => loc.clone(),
            AstNode::FnDef(_, _, _, _, loc) => loc.clone(),
            AstNode::If(_, _, loc) => loc.clone(),
            AstNode::While(_, _, loc) => loc.clone(),
            AstNode::Ref(_, _, loc) => loc.clone(),
            AstNode::Deref(_, loc) => loc.clone(),
        }
    }
}

pub fn parse(source: &str, file: &str) -> Result<Vec<AstNode>> {
    let pairs = SyntaxParser::parse(Rule::prog, source)?;
    let mut ast = Vec::new();

    for pair in pairs {
        //pair_tree(pair, 0);
        ast.push(build_ast(pair, file)?);
    }

    Ok(ast)
}

fn build_ast(pair: Pair<Rule>, file: &str) -> Result<AstNode> {
    match pair.as_rule() {
        Rule::number => Ok(AstNode::Number(pair.as_str().parse()?, to_loc(file, pair))),
        Rule::ident => Ok(AstNode::Ident(
            pair.as_str().trim().to_string(),
            to_loc(file, pair),
        )),
        Rule::string => Ok(AstNode::String(
            unescape_string(pair.as_str().trim_matches('"'))?,
            to_loc(file, pair),
        )),
        Rule::logic => {
            let mut pairs = pair.clone().into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap(), file)?;

            while let Some(op) = pairs.next() {
                let op = op.as_str().trim().to_string();
                let right = build_ast(pairs.next().unwrap(), file)?;

                left = AstNode::BinaryOp(
                    Box::new(left),
                    op,
                    Box::new(right),
                    to_loc(file, pair.clone()),
                )
            }

            Ok(left)
        }
        Rule::comparison => {
            let mut pairs = pair.clone().into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let left = build_ast(pairs.next().unwrap(), file)?;

            let first_pair = match pairs.next() {
                Some(p) => p,
                None => return Ok(left),
            };

            let current_op = first_pair.as_str().trim().to_string();
            let mut current_right = build_ast(pairs.next().unwrap(), file)?;

            let mut final_cmp = AstNode::Comparison(
                Box::new(left.clone()),
                current_op,
                Box::new(current_right.clone()),
                to_loc(file, pair.clone()),
            );

            while let Some(op) = pairs.next() {
                let next_left = current_right;
                let next_op = op.as_str().trim().to_string();
                let next_right = build_ast(pairs.next().unwrap(), file)?;

                let next_cmp = AstNode::Comparison(
                    Box::new(next_left),
                    next_op,
                    Box::new(next_right.clone()),
                    to_loc(file, pair.clone()),
                );

                final_cmp = AstNode::BinaryOp(
                    Box::new(final_cmp),
                    "&&".to_string(),
                    Box::new(next_cmp),
                    to_loc(file, pair.clone()),
                );

                current_right = next_right;
            }

            Ok(final_cmp)
        }
        Rule::expr => {
            let mut pairs = pair.clone().into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap(), file)?;

            while let Some(op) = pairs.next() {
                let op = match op.as_rule() {
                    Rule::PLUS => "+",
                    Rule::MINUS => "-",
                    _ => bail!("Unexpected operator: {op:?}"),
                };
                let right = build_ast(pairs.next().unwrap(), file)?;

                left = AstNode::BinaryOp(
                    Box::new(left),
                    op.to_string(),
                    Box::new(right),
                    to_loc(file, pair.clone()),
                );
            }

            Ok(left)
        }
        Rule::term => {
            let mut pairs = pair.clone().into_inner();
            if !(pairs.len() - 1).is_multiple_of(2) {
                return Err(ParserError::WrongPairCount(3, pairs.len()).into());
            }

            let mut left = build_ast(pairs.next().unwrap(), file)?;

            while let Some(op) = pairs.next() {
                let op = match op.as_rule() {
                    Rule::STAR => "*",
                    Rule::SLASH => "/",
                    Rule::PERCENT => "%",
                    _ => bail!("Unexpected operator: {op:?}"),
                };
                let right = build_ast(pairs.next().unwrap(), file)?;

                left = AstNode::BinaryOp(
                    Box::new(left),
                    op.to_string(),
                    Box::new(right),
                    to_loc(file, pair.clone()),
                );
            }

            Ok(left)
        }
        Rule::ref_expr => {
            let mut pairs = pair.clone().into_inner();
            let loc = to_loc(file, pair);

            let first = pairs.next().unwrap();
            let (mutable, expr_pair) = if matches!(first.as_rule(), Rule::mut_specifier) {
                (true, pairs.next().unwrap())
            } else {
                (false, first)
            };

            let expr = build_ast(expr_pair, file)?;
            Ok(AstNode::Ref(Box::new(expr), mutable, loc))
        }
        Rule::deref => {
            let mut pairs = pair.clone().into_inner();
            Ok(AstNode::Deref(
                Box::new(build_ast(pairs.next().unwrap(), file)?),
                to_loc(file, pair),
            ))
        }
        Rule::factor => {
            let mut pairs = pair.clone().into_inner();
            let first = pairs.next().expect("Need at least one pair");

            match first.as_rule() {
                Rule::MINUS | Rule::BANG => Ok(AstNode::UnaryOp(
                    Box::new(build_ast(
                        pairs.next().expect("Expected primary after factor"),
                        file,
                    )?),
                    first.as_str().trim().to_string(),
                    to_loc(file, pair),
                )),
                Rule::primary => build_ast(first, file),
                Rule::ref_expr => build_ast(first, file),
                _ => Err(anyhow::anyhow!("Unexpected rule: {:?}", first.as_rule())),
            }
        }
        Rule::primary => build_ast(pair.into_inner().next().unwrap(), file),
        Rule::let_stmt => {
            let mut pairs = pair.clone().into_inner();
            if pairs.len() < 2 && pairs.len() > 4 {
                return Err(ParserError::WrongPairCount(2, pairs.len()).into());
            }

            let next_pair = pairs.next().unwrap();
            let (name, mutability) = if matches!(next_pair.as_rule(), Rule::mut_specifier) {
                (pairs.next().unwrap().as_str().trim().to_string(), true)
            } else {
                (next_pair.as_str().trim().to_string(), false)
            };

            let next_pair = pairs.next().unwrap();
            if matches!(next_pair.as_rule(), Rule::data_type) {
                let type_pair = next_pair.clone();
                let expr = build_ast(pairs.next().unwrap(), file)?;
                Ok(AstNode::Let(
                    name,
                    mutability,
                    Some((
                        type_pair.as_str().trim().to_string(),
                        to_loc(file, type_pair),
                    )),
                    Box::new(expr),
                    to_loc(file, pair),
                ))
            } else {
                let expr = build_ast(next_pair, file)?;
                Ok(AstNode::Let(
                    name,
                    mutability,
                    None,
                    Box::new(expr),
                    to_loc(file, pair),
                ))
            }
        }
        Rule::assign_stmt => {
            let mut pairs = pair.clone().into_inner();
            if pairs.len() != 2 {
                return Err(ParserError::WrongPairCount(2, pairs.len()).into());
            }

            let name = build_ast(pairs.next().unwrap(), file)?;
            let expr = build_ast(pairs.next().unwrap(), file)?;
            Ok(AstNode::Assign(
                Box::new(name),
                Box::new(expr),
                to_loc(file, pair),
            ))
        }
        Rule::return_stmt => {
            let mut pairs = pair.clone().into_inner();
            if pairs.len() > 1 {
                return Err(ParserError::WrongPairCount(1, pairs.len()).into());
            }

            if pairs.len() == 0 {
                Ok(AstNode::Return(None, to_loc(file, pair)))
            } else {
                let expr = build_ast(pairs.next().unwrap(), file)?;
                Ok(AstNode::Return(Some(Box::new(expr)), to_loc(file, pair)))
            }
        }
        Rule::if_stmt => {
            let mut pairs = pair.clone().into_inner();
            let condition = build_ast(
                pairs.next().expect("If statement must have condition"),
                file,
            )?;

            let mut cond_pairs = Vec::new();
            cond_pairs.push((Box::new(condition), Vec::new()));
            let mut uncond_stmts = Vec::new();
            for p in pairs {
                match p.as_rule() {
                    Rule::else_if_stmt => {
                        let mut pairs = p.into_inner();
                        let condition = build_ast(
                            pairs.next().expect("If-Else statement must have condition"),
                            file,
                        )?;
                        cond_pairs.push((Box::new(condition), Vec::new()));

                        for p in pairs {
                            cond_pairs.last_mut().unwrap().1.push(build_ast(p, file)?);
                        }
                    }
                    Rule::else_stmt => {
                        for s in p.into_inner() {
                            uncond_stmts.push(build_ast(s, file)?);
                        }
                    }
                    _ => cond_pairs.last_mut().unwrap().1.push(build_ast(p, file)?),
                }
            }

            Ok(AstNode::If(cond_pairs, uncond_stmts, to_loc(file, pair)))
        }
        Rule::while_loop => {
            let mut pairs = pair.clone().into_inner();
            let condition = build_ast(pairs.next().expect("While loop must have condition"), file)?;

            Ok(AstNode::While(
                Box::new(condition),
                pairs.map(|p| build_ast(p, file).unwrap()).collect(),
                to_loc(file, pair),
            ))
        }
        Rule::call => {
            let mut pairs = pair.clone().into_inner();

            let name = pairs
                .next()
                .expect("Must specify name of function to call")
                .as_str()
                .trim()
                .to_string();

            let mut args = Vec::with_capacity(pairs.len());

            for p in pairs {
                args.push(build_ast(p, file)?);
            }

            Ok(AstNode::Call(name, args, to_loc(file, pair)))
        }
        Rule::fn_def => {
            let mut pairs = pair.clone().into_inner();

            let name = pairs
                .next()
                .expect("Function definition must include name")
                .as_str()
                .trim()
                .to_string();

            let mut args = Vec::new();
            let mut body = Vec::new();
            let mut return_type = None;
            while let Some(p) = pairs.next() {
                if matches!(p.as_rule(), Rule::ident) {
                    let start = p.as_span().start();
                    let name = p.as_str().trim().to_string();
                    let p = pairs.next().unwrap();
                    let end = p.as_span().end();
                    args.push((
                        name,
                        p.as_str().trim().to_string(),
                        (file.to_string(), start..end),
                    ));
                } else if matches!(p.as_rule(), Rule::data_type) {
                    return_type = Some(p.as_str().trim().to_string())
                } else if matches!(p.as_rule(), Rule::stmt) {
                    body.push(build_ast(p, file)?);
                } else {
                    bail!(
                        "Unexpected node, expected either ident or stmt, found: {:?}",
                        p.as_rule()
                    );
                }
            }

            Ok(AstNode::FnDef(
                name,
                args,
                return_type,
                body,
                to_loc(file, pair),
            ))
        }
        Rule::stmt => Ok(build_ast(pair.into_inner().next().unwrap(), file)?),
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
