use crate::bytecode::operand::{MemOrConstant, MemOrFp};

/// Conditional jump: `JumpUnlessZero`. Jumps if `condition != 0`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JumpIfNotZeroInstruction {
    /// The value to check. The jump is taken if this value is not zero.
    pub condition: MemOrConstant,
    /// The destination `pc` for the jump.
    pub dest: MemOrConstant,
    /// The new value for the frame pointer (`fp`) after the instruction.
    pub updated_fp: MemOrFp,
}
