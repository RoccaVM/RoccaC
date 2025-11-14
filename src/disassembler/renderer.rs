use crossterm::event::{self, Event, KeyCode};
use ratatui::{
    Frame,
    layout::{Constraint, Direction, Layout, Rect},
    style::{Color, Modifier, Style},
    text::{Line, Span},
    widgets::{Block, Borders, List, ListItem, Paragraph},
};
use std::time::Duration;

use crate::bytecode::{BytecodeFile, Constant, Function, Opcode};

#[derive(Debug, Clone)]
struct Instruction {
    address: usize,
    bytes: Vec<u8>,
    opcode: Opcode,
    operands: Vec<String>,
    inline_info: String,
}

pub struct Renderer {
    bytecode: BytecodeFile,
    selected_function: Option<usize>,
    functions: Vec<Function>,

    /// decoded instructions of the currently selected function
    instructions: Vec<Instruction>,
    cursor: usize,
    scroll: usize,
}

impl Renderer {
    pub fn new(bytecode: BytecodeFile) -> Self {
        let functions = bytecode.functions.clone();

        Self {
            bytecode,
            selected_function: None,
            functions,
            instructions: vec![],
            cursor: 0,
            scroll: 0,
        }
    }

    fn decode_function(&mut self, func: &Function) {
        let mut i = 0;
        let mut out = Vec::new();
        while i < func.code.len() {
            let addr = i;
            let opcode = Opcode::try_from(func.code[i]).unwrap();
            let mut bytes = vec![func.code[i]];
            i += 1;

            let mut operands = Vec::new();
            let mut inline_info = String::new();

            match opcode {
                Opcode::ConstI64 => {
                    let val_bytes = &func.code[i..i + 4];
                    bytes.extend_from_slice(val_bytes);
                    let val = u32::from_le_bytes(val_bytes.try_into().unwrap());
                    operands.push(format!("#{val}"));
                    inline_info = format!("Load const #{val}");
                    i += 4;
                }
                Opcode::ConstString => {
                    let val_bytes = &func.code[i..i + 4];
                    bytes.extend_from_slice(val_bytes);
                    let val = u32::from_le_bytes(val_bytes.try_into().unwrap());
                    operands.push(format!("#{val}"));
                    inline_info = format!("Load const #{val}");
                    i += 4;
                }
                Opcode::LoadLocal | Opcode::StoreLocal => {
                    let val_bytes = &func.code[i..i + 2];
                    bytes.extend_from_slice(val_bytes);
                    let idx = u16::from_le_bytes(val_bytes.try_into().unwrap());
                    operands.push(format!("local[{idx}]"));
                    inline_info = format!("Access local var {idx}");
                    i += 2;
                }
                Opcode::Call | Opcode::CallNative => {
                    let val_bytes = &func.code[i..i + 5];
                    bytes.extend_from_slice(val_bytes);
                    let idx = u32::from_le_bytes(val_bytes[..4].try_into().unwrap());
                    let argc = val_bytes[4];
                    operands.push(format!("fn[{idx}], argc={argc}"));
                    inline_info = format!("Call fn#{idx} with {argc} args");
                    i += 5;
                }
                _ => {}
            }

            out.push(Instruction {
                address: addr,
                bytes,
                opcode,
                operands,
                inline_info,
            });
        }

        self.instructions = out;
    }

    pub fn handle_input(&mut self) -> anyhow::Result<bool> {
        if event::poll(Duration::from_millis(16))?
            && let Event::Key(key) = event::read()?
        {
            match key.code {
                KeyCode::Char('q') => return Ok(true),
                KeyCode::Down => {
                    if let Some(_) = self.selected_function
                        && self.cursor + 1 < self.instructions.len()
                    {
                        self.cursor += 1;
                        if self.cursor >= self.scroll + 20 {
                            self.scroll += 1;
                        }
                    }
                }
                KeyCode::Up => {
                    if let Some(_) = self.selected_function
                        && self.cursor > 0
                    {
                        self.cursor -= 1;
                        if self.cursor < self.scroll {
                            self.scroll = self.scroll.saturating_sub(1);
                        }
                    }
                }
                KeyCode::Tab => {
                    // move to next function
                    let next_idx = match self.selected_function {
                        Some(i) => (i + 1) % self.functions.len(),
                        None => 0,
                    };
                    self.selected_function = Some(next_idx);
                    self.decode_function(&self.functions[next_idx].clone());
                    self.cursor = 0;
                    self.scroll = 0;
                }
                _ => {}
            }
        }
        Ok(false)
    }

    pub fn render(&self, f: &mut Frame, area: Rect) {
        let columns = Layout::default()
            .direction(Direction::Horizontal)
            .constraints([
                Constraint::Percentage(25),
                Constraint::Percentage(50),
                Constraint::Percentage(25),
            ])
            .split(area);

        self.render_left_pane(f, columns[0]);
        self.render_middle_pane(f, columns[1]);
        self.render_right_pane(f, columns[2]);
    }

    fn render_left_pane(&self, f: &mut Frame, area: Rect) {
        let left_chunks = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Percentage(50), Constraint::Percentage(50)])
            .split(area);

        // Constants
        let const_lines: Vec<Line> = self
            .bytecode
            .const_pool
            .iter()
            .enumerate()
            .map(|(i, c)| {
                Line::from(Span::raw(format!(
                    "{i:02}: {}",
                    match c {
                        Constant::Int(v) => format!("Int({v})"),
                        Constant::String(s) => format!("Str({s})"),
                    }
                )))
            })
            .collect();

        let const_view = Paragraph::new(const_lines)
            .block(Block::default().title("Constants").borders(Borders::ALL));

        // Function list
        let func_items: Vec<ListItem> = self
            .functions
            .iter()
            .enumerate()
            .map(|(i, f)| {
                let style = if Some(i) == self.selected_function {
                    Style::default().fg(Color::Black).bg(Color::Cyan)
                } else {
                    Style::default().fg(Color::Gray)
                };
                ListItem::new(Line::styled(f.name.to_string(), style))
            })
            .collect();

        let func_list =
            List::new(func_items).block(Block::default().title("Functions").borders(Borders::ALL));

        f.render_widget(const_view, left_chunks[0]);
        f.render_widget(func_list, left_chunks[1]);
    }

    fn render_middle_pane(&self, f: &mut Frame, area: Rect) {
        let title = if let Some(idx) = self.selected_function {
            format!("Disassembly: {}", self.functions[idx].name)
        } else {
            "Disassembly (no function selected)".to_string()
        };

        let lines: Vec<Line> = if self.selected_function.is_some() {
            self.instructions
                .iter()
                .enumerate()
                .skip(self.scroll)
                .take(25)
                .map(|(i, instr)| {
                    let addr = format!("{:04X}", instr.address);
                    let hex_bytes = instr
                        .bytes
                        .iter()
                        .map(|b| format!("{b:02X}"))
                        .collect::<Vec<_>>()
                        .join(" ");
                    let disas = format!("{:?}", instr.opcode);
                    let ops = instr.operands.join(", ");
                    let line = format!("{addr}:  {hex_bytes:<12}  {disas:<8}  {ops}");

                    let style = if i == self.cursor {
                        Style::default()
                            .fg(Color::Black)
                            .bg(Color::Cyan)
                            .add_modifier(Modifier::BOLD)
                    } else {
                        Style::default().fg(Color::Gray)
                    };

                    Line::from(Span::styled(line, style))
                })
                .collect()
        } else {
            vec![Line::from(Span::styled(
                "Select a function from the left pane (TAB)",
                Style::default().fg(Color::DarkGray),
            ))]
        };

        let paragraph =
            Paragraph::new(lines).block(Block::default().title(title).borders(Borders::ALL));

        f.render_widget(paragraph, area);
    }

    fn render_right_pane(&self, f: &mut Frame, area: Rect) {
        let title = "Instruction Details";
        let lines = if let (Some(_), Some(instr)) =
            (self.selected_function, self.instructions.get(self.cursor))
        {
            vec![
                Line::from(format!("Address: 0x{:04X}", instr.address)),
                Line::from(format!("Opcode: {:?}", instr.opcode)),
                Line::from(format!(
                    "Bytes: {}",
                    instr
                        .bytes
                        .iter()
                        .map(|b| format!("{b:02X}"))
                        .collect::<Vec<_>>()
                        .join(" ")
                )),
                Line::from(format!("Operands: {}", instr.operands.join(", "))),
                Line::from(format!("Info: {}", instr.inline_info)),
            ]
        } else {
            vec![Line::from(Span::styled(
                "No instruction selected",
                Style::default().fg(Color::DarkGray),
            ))]
        };

        let paragraph =
            Paragraph::new(lines).block(Block::default().title(title).borders(Borders::ALL));

        f.render_widget(paragraph, area);
    }
}
