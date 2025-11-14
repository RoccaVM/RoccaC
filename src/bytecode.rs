use std::io::{Read, Write};

use anyhow::Result;
use bitfield_struct::bitfield;
use num_enum::TryFromPrimitive;

pub const MAGIC: u32 = 0x424D4352;
pub const VERSION: u16 = 1;

#[derive(Clone, Debug)]
pub struct BytecodeFile {
    pub header: Header,
    pub const_pool: Vec<Constant>,
    pub functions: Vec<Function>,
    pub entrypoint: u32,
}

#[bitfield(u16)]
pub struct Flags {
    #[bits(1)]
    pub debug_symbols: bool,

    #[bits(15)]
    _padding: u16,
}

#[derive(Clone, Debug)]
pub struct Header {
    pub magic: u32,
    pub version: u16,
    pub flags: Flags,
}

#[derive(Clone, Debug)]
pub enum Constant {
    Int(i64),
    String(String),
}

#[derive(Clone, Debug)]
pub struct Function {
    pub name: String,
    pub arity: u8,
    pub locals_count: u16,
    pub max_stack: u16,
    pub code: Vec<u8>,
}

#[derive(Clone, Eq, PartialEq, TryFromPrimitive, Debug)]
#[repr(u8)]
pub enum Opcode {
    // Stack
    Nop = 0x00,
    Pop = 0x01,
    Dup = 0x02,

    // Consts
    ConstI64 = 0x10,
    ConstString = 0x12,

    // Locals
    LoadLocal = 0x20,
    StoreLocal = 0x21,

    // Aritmetic
    Add = 0x30,
    Sub = 0x31,
    Mul = 0x32,
    Div = 0x34,

    // Logic
    And = 0x40,
    Or = 0x41,
    Not = 0x42,

    // Compare
    Eq = 0x50,
    Ne = 0x51,

    // Flow
    Jump = 0x60,
    Call = 0x61,
    Ret = 0x62,
    CallNative = 0x63,
}

impl Default for BytecodeFile {
    fn default() -> Self {
        Self {
            header: Header {
                magic: MAGIC,
                version: VERSION,
                flags: Flags::new(),
            },
            const_pool: Vec::new(),
            functions: Vec::new(),
            entrypoint: 0,
        }
    }
}

impl BytecodeFile {
    pub fn new(entrypoint: u32) -> Self {
        BytecodeFile {
            entrypoint,
            ..Default::default()
        }
    }

    pub fn write<W: Write>(&self, writer: &mut W) -> Result<()> {
        writer.write_all(&self.header.magic.to_le_bytes())?;
        writer.write_all(&self.header.version.to_le_bytes())?;
        let flags: u16 = self.header.flags.into();
        writer.write_all(&flags.to_le_bytes())?;

        writer.write_all(&(self.const_pool.len() as u32).to_le_bytes())?;
        for c in &self.const_pool {
            match c {
                Constant::Int(val) => {
                    writer.write_all(&[0x00])?;
                    writer.write_all(&val.to_le_bytes())?;
                }
                Constant::String(val) => {
                    writer.write_all(&[0x02])?;
                    writer.write_all(&(val.len() as u32).to_le_bytes())?;
                    writer.write_all(val.as_bytes())?;
                }
            }
        }

        writer.write_all(&(self.functions.len() as u32).to_le_bytes())?;
        for func in &self.functions {
            if self.header.flags.debug_symbols() {
                writer.write_all(&[func.name.len() as u8])?;
                writer.write_all(func.name.as_bytes())?;
            }

            writer.write_all(&[func.arity])?;
            writer.write_all(&func.locals_count.to_le_bytes())?;
            writer.write_all(&func.max_stack.to_le_bytes())?;

            writer.write_all(&(func.code.len() as u32).to_le_bytes())?;
            writer.write_all(&func.code)?;
        }

        writer.write_all(&self.entrypoint.to_le_bytes())?;

        Ok(())
    }

    pub fn read<R: Read>(reader: &mut R) -> Result<Self> {
        let mut magic_bytes = [0u8; 4];
        reader.read_exact(&mut magic_bytes)?;

        if u32::from_le_bytes(magic_bytes) != MAGIC {
            anyhow::bail!("Invalid magic number");
        }

        let mut version_bytes = [0u8; 2];
        reader.read_exact(&mut version_bytes)?;

        let version = u16::from_le_bytes(version_bytes);
        if version != VERSION {
            anyhow::bail!("Wrong bytecode version: expected {VERSION} got {version}");
        }

        let mut flag_bytes = [0u8; 2];
        reader.read_exact(&mut flag_bytes)?;
        let flags = u16::from_le_bytes(flag_bytes);
        let flags = Flags::from(flags);

        let mut const_count_bytes = [0u8; 4];
        reader.read_exact(&mut const_count_bytes)?;

        let const_count = u32::from_le_bytes(const_count_bytes);
        let mut constants = Vec::with_capacity(const_count as usize);
        for _ in 0..const_count {
            let mut type_tag = [0u8; 1];
            reader.read_exact(&mut type_tag)?;

            let constant = match type_tag[0] {
                0x00 => {
                    let mut val_bytes = [0u8; 8];
                    reader.read_exact(&mut val_bytes)?;
                    Constant::Int(i64::from_le_bytes(val_bytes))
                }
                0x02 => {
                    let mut string_length_bytes = [0u8; 4];
                    reader.read_exact(&mut string_length_bytes)?;
                    let mut string_bytes =
                        vec![0u8; u32::from_le_bytes(string_length_bytes) as usize];
                    reader.read_exact(&mut string_bytes)?;
                    Constant::String(String::from_utf8(string_bytes)?)
                }
                _ => {
                    anyhow::bail!("Unknown constant type: {}", type_tag[0]);
                }
            };

            constants.push(constant);
        }

        let mut func_count_bytes = [0u8; 4];
        reader.read_exact(&mut func_count_bytes)?;

        let func_count = u32::from_le_bytes(func_count_bytes);
        let mut funcs = Vec::with_capacity(func_count as usize);
        for _ in 0..func_count {
            let name = if flags.debug_symbols() {
                let mut func_len_bytes = [0u8; 1];
                reader.read_exact(&mut func_len_bytes)?;
                let mut func_name_bytes = vec![0u8; func_len_bytes[0] as usize];
                reader.read_exact(&mut func_name_bytes)?;
                String::from_utf8(func_name_bytes)?
            } else {
                "".to_string()
            };

            let mut arity_bytes = [0u8; 1];
            reader.read_exact(&mut arity_bytes)?;

            let mut locals_count_bytes = [0u8; 2];
            reader.read_exact(&mut locals_count_bytes)?;
            let locals_count = u16::from_le_bytes(locals_count_bytes);

            let mut max_stack_bytes = [0u8, 2];
            reader.read_exact(&mut max_stack_bytes)?;
            let max_stack = u16::from_le_bytes(max_stack_bytes);

            let mut code_length_bytes = [0u8; 4];
            reader.read_exact(&mut code_length_bytes)?;
            let mut code = vec![0u8; u32::from_le_bytes(code_length_bytes) as usize];
            reader.read_exact(&mut code)?;

            funcs.push(Function {
                name,
                arity: arity_bytes[0],
                locals_count,
                max_stack,
                code,
            });
        }

        let mut entrypoint_bytes = [0u8; 4];
        reader.read_exact(&mut entrypoint_bytes)?;
        let entrypoint = u32::from_le_bytes(entrypoint_bytes);

        Ok(BytecodeFile {
            header: Header {
                magic: MAGIC,
                version: VERSION,
                flags,
            },
            const_pool: constants,
            functions: funcs,
            entrypoint,
        })
    }
}
