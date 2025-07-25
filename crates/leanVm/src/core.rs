use crate::{context::run_context::RunContext, memory::manager::MemoryManager};

#[derive(Debug, Default)]
pub struct VirtualMachine {
    pub(crate) run_context: RunContext,
    pub memory_manager: MemoryManager,
}
