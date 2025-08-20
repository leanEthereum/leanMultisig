use std::collections::BTreeMap;

use crate::lang::Label;

#[derive(Debug)]
pub struct Compiler {
    pub memory_size_per_function: BTreeMap<String, usize>,
    pub label_to_pc: BTreeMap<Label, usize>,
}
