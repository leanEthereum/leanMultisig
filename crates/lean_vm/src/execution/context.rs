use crate::core::SourceLineNumber;
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct ExecutionHistory {
    pub lines: Vec<SourceLineNumber>,
    pub cycles: Vec<usize>, // for each line, how many cycles it took
}

impl ExecutionHistory {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_line(&mut self, location: SourceLineNumber, cycles: usize) {
        self.lines.push(location);
        self.cycles.push(cycles);
    }

    pub fn total_cycles(&self) -> usize {
        self.cycles.iter().sum()
    }

    pub const fn len(&self) -> usize {
        self.lines.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.lines.is_empty()
    }
}

#[derive(Debug)]
pub struct ExecutionContext<'a> {
    pub source_code: &'a str,
    pub function_locations: &'a BTreeMap<usize, String>,
    pub profiler_enabled: bool,
    pub std_out: String,
    pub instruction_history: ExecutionHistory,
}

impl<'a> ExecutionContext<'a> {
    pub fn new(
        source_code: &'a str,
        function_locations: &'a BTreeMap<usize, String>,
        profiler_enabled: bool,
    ) -> Self {
        Self {
            source_code,
            function_locations,
            profiler_enabled,
            std_out: String::new(),
            instruction_history: ExecutionHistory::new(),
        }
    }

    pub fn print(&mut self, message: &str) {
        self.std_out.push_str(message);
    }

    pub fn println(&mut self, message: &str) {
        self.std_out.push_str(message);
        self.std_out.push('\n');
    }
}
