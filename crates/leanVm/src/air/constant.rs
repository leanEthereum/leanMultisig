use lean_isa::precompiles::PRECOMPILES;

/// The total number of columns that represent a single instruction in the bytecode ROM.
pub(crate) const N_INSTRUCTION_COLUMNS: usize = 15;
/// The number of columns in the execution trace that are directly committed by the prover.
pub(crate) const N_COMMITTED_EXEC_COLUMNS: usize = 5;
/// The number of "virtual" columns that hold memory values, derived via lookups.
///
/// virtual (lookup into memory, with logup*)
pub(crate) const N_MEMORY_VALUE_COLUMNS: usize = 3;
/// The total number of columns related to the execution state (committed + virtual).
pub(crate) const N_EXEC_COLUMNS: usize = N_COMMITTED_EXEC_COLUMNS + N_MEMORY_VALUE_COLUMNS;
/// The number of instruction columns included in the AIR, excluding precompile-specific flags.
pub(crate) const N_INSTRUCTION_COLUMNS_IN_AIR: usize = N_INSTRUCTION_COLUMNS - PRECOMPILES.len();
/// The total width of the AIR table for the main CPU, combining instruction and execution columns.
pub(crate) const N_EXEC_AIR_COLUMNS: usize = N_INSTRUCTION_COLUMNS_IN_AIR + N_EXEC_COLUMNS;
/// The total number of columns in the combined trace (instruction + execution).
pub(crate) const N_TOTAL_COLUMNS: usize = N_INSTRUCTION_COLUMNS + N_EXEC_COLUMNS;

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
/// The opcode flag that activates the Poseidon16 precompile's constraints.
pub(crate) const COL_INDEX_POSEIDON_16: usize = 11;
/// The opcode flag that activates the Poseidon24 precompile's constraints.
pub(crate) const COL_INDEX_POSEIDON_24: usize = 12;
/// The opcode flag that activates the DotProduct precompile's constraints.
pub(crate) const COL_INDEX_DOT_PRODUCT: usize = 13;
/// The opcode flag that activates the MultilinearEval precompile's constraints.
pub(crate) const COL_INDEX_MULTILINEAR_EVAL: usize = 14;

/// The total number of columns representing a single decoded instruction from the bytecode.
pub(crate) const N_BYTECODE_COLUMNS: usize = 15;

// Execution trace columns (committed by the prover)

/// The column for the Program Counter (pc) register in the execution trace.
pub(crate) const COL_INDEX_PC: usize = N_BYTECODE_COLUMNS + 3;
/// The column for the Frame Pointer (fp) register in the execution trace.
pub(crate) const COL_INDEX_FP: usize = N_BYTECODE_COLUMNS + 4;
/// The column holding the memory address for operand `a` when `FLAG_A` is 0.
pub(crate) const COL_INDEX_MEM_ADDRESS_A: usize = N_BYTECODE_COLUMNS + 5;
/// The column holding the memory address for operand `b` when `FLAG_B` is 0.
pub(crate) const COL_INDEX_MEM_ADDRESS_B: usize = N_BYTECODE_COLUMNS + 6;
/// The column holding the memory address for operand `c` when `FLAG_C` is 0.
pub(crate) const COL_INDEX_MEM_ADDRESS_C: usize = N_BYTECODE_COLUMNS + 7;
/// The total count of columns in the execution trace that are directly committed by the prover.
pub(crate) const N_REAL_EXEC_COLUMNS: usize = 5;

// Virtual columns (derived via lookups, not committed directly)

/// The virtual column holding the value read from memory for operand `a`.
pub(crate) const COL_INDEX_MEM_VALUE_A: usize = N_BYTECODE_COLUMNS;
/// The virtual column holding the value read from memory for operand `b`.
pub(crate) const COL_INDEX_MEM_VALUE_B: usize = N_BYTECODE_COLUMNS + 1;
/// The virtual column holding the value read from memory for operand `c`.
pub(crate) const COL_INDEX_MEM_VALUE_C: usize = N_BYTECODE_COLUMNS + 2;
