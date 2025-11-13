use crate::bytecode::{BytecodeFile, Function};

pub enum Panel {
    Constants,
    Code,
}

pub struct DisasmState {
    pub bytecode: BytecodeFile,
    pub selected_func: usize,
    pub scroll: usize,
    pub active_panel: Panel,
}

impl Default for DisasmState {
    fn default() -> Self {
        Self::new(BytecodeFile::new(0))
    }
}

impl DisasmState {
    pub fn new(bytecode: BytecodeFile) -> Self {
        Self {
            bytecode,
            selected_func: 0,
            scroll: 0,
            active_panel: Panel::Code,
        }
    }

    pub fn current_func(&self) -> Option<&Function> {
        self.bytecode.functions.get(self.selected_func)
    }

    pub fn scroll_up(&mut self) {
        if self.scroll > 0 {
            self.scroll -= 1;
        }
    }

    pub fn scroll_down(&mut self) {
        self.scroll += 1;
    }

    pub fn next_panel(&mut self) {
        self.active_panel = match self.active_panel {
            Panel::Constants => Panel::Code,
            Panel::Code => Panel::Constants,
        }
    }
}
