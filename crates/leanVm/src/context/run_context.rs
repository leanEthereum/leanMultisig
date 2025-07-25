use crate::memory::address::MemoryAddress;

#[derive(Debug)]
pub struct RunContext {
    /// The address in memory of the current instruction to be executed.
    pub(crate) pc: MemoryAddress,
    /// Points to the beginning of the stack frame of the current function.
    ///
    /// The value of `fp` stays the same fopr all the instructions in the same invocation of a function.
    pub(crate) fp: MemoryAddress,
}

impl RunContext {
    #[must_use]
    pub const fn new(pc: MemoryAddress, fp: MemoryAddress) -> Self {
        Self { pc, fp }
    }

    #[must_use]
    pub const fn pc(&self) -> &MemoryAddress {
        &self.pc
    }

    #[must_use]
    pub const fn fp(&self) -> &MemoryAddress {
        &self.fp
    }
}
