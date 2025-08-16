// Bytecode columns (looked up from the program ROM)

/// The immediate value or memory offset for the first operand, `a`.
pub(crate) const COL_INDEX_OPERAND_A: usize = 0;
/// The immediate value or memory offset for the second operand, `b`.
pub(crate) const COL_INDEX_OPERAND_B: usize = 1;
/// The immediate value or memory offset for the third operand, `c`.
pub(crate) const COL_INDEX_OPERAND_C: usize = 2;
/// A boolean flag selecting between the immediate `OPERAND_A` (1) and a memory value (0).
pub(crate) const COL_INDEX_FLAG_A: usize = 3;
/// A boolean flag selecting between the immediate `OPERAND_B` (1) and a memory value (0).
pub(crate) const COL_INDEX_FLAG_B: usize = 4;
/// A boolean flag selecting between `fp` or an immediate `OPERAND_C` (1) and a memory value (0).
pub(crate) const COL_INDEX_FLAG_C: usize = 5;
/// The opcode flag that activates the ADD instruction's constraints.
pub(crate) const COL_INDEX_ADD: usize = 6;
/// The opcode flag that activates the MUL instruction's constraints.
pub(crate) const COL_INDEX_MUL: usize = 7;
/// The opcode flag that activates the DEREF instruction's constraints.
pub(crate) const COL_INDEX_DEREF: usize = 8;
/// The opcode flag that activates the JUZ (Jump Unless Zero) instruction's constraints.
pub(crate) const COL_INDEX_JUZ: usize = 9;
/// An auxiliary operand used for multi-purpose logic, like specifying the `res` type in DEREF.
pub(crate) const COL_INDEX_AUX: usize = 10;
/// The total number of columns representing a single decoded instruction from the bytecode.
pub(crate) const N_BYTECODE_COLUMNS: usize = 11;

// Execution trace columns (committed by the prover)

/// The column for the Program Counter (pc) register in the execution trace.
pub(crate) const COL_INDEX_PC: usize = N_BYTECODE_COLUMNS + 3;
/// The column for the Frame Pointer (fp) register in the execution trace.
pub(crate) const COL_INDEX_FP: usize = N_BYTECODE_COLUMNS + 4;
/// The column holding the memory address for operand `a` when `FLAG_A` is 0.
pub(crate) const COL_INDEX_ADDR_A: usize = N_BYTECODE_COLUMNS + 5;
/// The column holding the memory address for operand `b` when `FLAG_B` is 0.
pub(crate) const COL_INDEX_ADDR_B: usize = N_BYTECODE_COLUMNS + 6;
/// The column holding the memory address for operand `c` when `FLAG_C` is 0.
pub(crate) const COL_INDEX_ADDR_C: usize = N_BYTECODE_COLUMNS + 7;
/// The total count of columns in the execution trace that are directly committed by the prover.
pub(crate) const N_REAL_EXEC_COLUMNS: usize = 5;

// Virtual columns (derived via lookups, not committed directly)

/// The virtual column holding the value read from memory for operand `a`.
pub(crate) const COL_INDEX_MEM_VALUE_A: usize = N_BYTECODE_COLUMNS;
/// The virtual column holding the value read from memory for operand `b`.
pub(crate) const COL_INDEX_MEM_VALUE_B: usize = N_BYTECODE_COLUMNS + 1;
/// The virtual column holding the value read from memory for operand `c`.
pub(crate) const COL_INDEX_MEM_VALUE_C: usize = N_BYTECODE_COLUMNS + 2;

/// The total number of columns in the AIR, including bytecode, real, and virtual columns.
pub(crate) const N_EXEC_AIR_COLUMNS: usize = N_BYTECODE_COLUMNS + 3 + N_REAL_EXEC_COLUMNS;
