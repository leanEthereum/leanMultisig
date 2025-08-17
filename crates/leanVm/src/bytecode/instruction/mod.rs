use computation::ComputationInstruction;
use deref::DerefInstruction;
use dot_product::DotProductInstruction;
use jump::JumpIfNotZeroInstruction;
use multilinear_eval::MultilinearEvalInstruction;
use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use poseidon16::Poseidon2_16Instruction;
use poseidon24::Poseidon2_24Instruction;

use super::operand::{MemOrConstant, MemOrFp, MemOrFpOrConstant};
use crate::{
    air::constant::{
        COL_INDEX_ADD, COL_INDEX_AUX, COL_INDEX_DEREF, COL_INDEX_FLAG_A, COL_INDEX_FLAG_B,
        COL_INDEX_FLAG_C, COL_INDEX_JUZ, COL_INDEX_MUL, COL_INDEX_OPERAND_A, COL_INDEX_OPERAND_B,
        COL_INDEX_OPERAND_C, N_INSTRUCTION_COLUMNS,
    },
    bytecode::operation::Operation,
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::manager::MemoryManager,
    witness::Witness,
};

pub mod computation;
pub mod deref;
pub mod dot_product;
pub mod jump;
pub mod multilinear_eval;
pub mod poseidon16;
pub mod poseidon24;

/// Defines the instruction set for this zkVM, specialized for the `AggregateMerge` logic.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    /// Performs a basic arithmetic computation: `res = arg_a op arg_b`.
    ///
    /// This corresponds to the `ADD` and `MUL` opcodes in the design document.
    Computation(ComputationInstruction),
    /// Performs a memory dereference: `res = m[m[fp + shift_0] + shift_1]`.
    ///
    /// This corresponds to the `DEREF` opcode.
    Deref(DerefInstruction),
    /// A conditional jump, called `JUZ` (Jump Unless Zero).
    ///
    /// Changes the `pc` if `condition` is non-zero.
    JumpIfNotZero(JumpIfNotZeroInstruction),
    /// **Precompile** for a Poseidon2 permutation over 16 base field elements.
    ///
    /// This is used for hashing operations within the `AggregateMerge` algorithm.
    /// The precompile performs: `Poseidon2(m'[m[fp+s]], m'[m[fp+s+1]]) = (m'[m[fp+s+2]], m'[m[fp+s+3]])`,
    /// where:
    /// - `s` is the shift,
    /// - `m` is scalar memory,
    /// - `m'` is vectorized memory access (a chunk of 8 base field elements, representing a degree-8 extension field element).
    Poseidon2_16(Poseidon2_16Instruction),
    /// **Precompile** for a Poseidon2 permutation over 24 base field elements.
    ///
    /// This operates similarly to `Poseidon2_16` but on 3 concatenated input vectors and 3 output vectors.
    ///
    /// It reads 6 pointers from memory, starting at `m[fp+shift]`.
    Poseidon2_24(Poseidon2_24Instruction),

    /// Dot product of two vectors of extension field elements.
    DotProduct(DotProductInstruction),

    /// Evaluation of a multilinear polynomial over the extension field.
    MultilinearEval(MultilinearEvalInstruction),
}

impl Instruction {
    /// Executes a single instruction, forming one step of the VM's execution cycle.
    ///
    /// This function is the engine of the virtual machine. It orchestrates the two main phases
    /// of a single step: execution and register update.
    ///
    /// 1.  **Execution:** It first matches on the `instruction` variant to dispatch to the appropriate
    ///     helper method. These helpers are responsible for fetching operands, performing the instruction's core logic, and
    ///     verifying any required assertions (e.g., that a computed value matches an expected one).
    ///
    /// 2.  **Register Update:** If the execution phase completes successfully, this function then
    ///     calls `update_registers` to advance the program counter (`pc`) and frame pointer (`fp`)
    ///     to prepare for the next instruction.
    pub fn execute<Perm16, Perm24>(
        &self,
        run_context: &RunContext,
        memory_manager: &mut MemoryManager,
        perm16: &Perm16,
        perm24: &Perm24,
    ) -> Result<(), VirtualMachineError>
    where
        Perm16: Permutation<[F; 2 * DIMENSION]>,
        Perm24: Permutation<[F; 3 * DIMENSION]>,
    {
        // Dispatch to the appropriate execution logic based on the instruction type.
        match self {
            // Handle arithmetic operations like ADD and MUL.
            Self::Computation(instruction) => instruction.execute(run_context, memory_manager),
            // Handle double-dereference memory operations.
            Self::Deref(instruction) => instruction.execute(run_context, memory_manager),
            // The `JumpIfNotZero` instruction has no execution logic; its effects
            // (changing pc and fp) are handled entirely within the register update phase.
            Self::JumpIfNotZero(_) => Ok(()),
            // Handle the Poseidon2 (16-element) precompile.
            Self::Poseidon2_16(instruction) => {
                instruction.execute(run_context, memory_manager, perm16)
            }
            // Handle the Poseidon2 (24-element) precompile.
            Self::Poseidon2_24(instruction) => {
                instruction.execute(run_context, memory_manager, perm24)
            }
            // Handle the dot product precompile.
            Self::DotProduct(instruction) => instruction.execute(run_context, memory_manager),
            // Handle the multilinear evaluation precompile.
            Self::MultilinearEval(instruction) => instruction.execute(run_context, memory_manager),
        }
    }

    /// Generates a witness for a precompile instruction, if applicable.
    ///
    /// This function checks the instruction type and, if it's a precompile, it calls the
    /// corresponding `generate_witness` method to capture the necessary data for the proof.
    /// For standard instructions, it returns `Ok(None)`.
    pub fn generate_witness(
        &self,
        cycle: usize,
        run_context: &RunContext,
        memory_manager: &MemoryManager,
    ) -> Result<Option<Witness>, VirtualMachineError> {
        match self {
            // If the instruction is Poseidon2_16, generate its witness.
            Self::Poseidon2_16(instruction) => Ok(Some(Witness::Poseidon16(
                instruction.generate_witness(cycle, run_context, memory_manager)?,
            ))),
            // If the instruction is Poseidon2_24, generate its witness.
            Self::Poseidon2_24(instruction) => Ok(Some(Witness::Poseidon24(
                instruction.generate_witness(cycle, run_context, memory_manager)?,
            ))),
            // If the instruction is a DotProduct, generate its witness.
            Self::DotProduct(instruction) => Ok(Some(Witness::DotProduct(
                instruction.generate_witness(cycle, run_context, memory_manager)?,
            ))),
            // If the instruction is a MultilinearEval, generate its witness.
            Self::MultilinearEval(instruction) => Ok(Some(Witness::MultilinearEval(
                instruction.generate_witness(cycle, run_context, memory_manager)?,
            ))),
            // For all other instruction types, no special witness is generated.
            _ => Ok(None),
        }
    }

    /// Converts an instruction into its raw field representation for the execution trace.
    #[must_use]
    pub fn field_representation(&self) -> Vec<F> {
        // Initialize a vector of zeros for all instruction-related columns.
        let mut repr = vec![F::ZERO; N_INSTRUCTION_COLUMNS];

        // Populate the vector based on the instruction type.
        match self {
            Self::Computation(ComputationInstruction {
                operation,
                arg_a,
                arg_b,
                res,
            }) => {
                // Set the appropriate opcode flag for ADD or MUL.
                match operation {
                    Operation::Add => repr[COL_INDEX_ADD] = F::ONE,
                    Operation::Mul => repr[COL_INDEX_MUL] = F::ONE,
                }
                // Convert operands to their field and flag representations.
                let (op_a, flag_a) = op_to_field(arg_a);
                let (op_b, flag_b) = op_to_field_fp(arg_b);
                let (op_c, flag_c) = op_to_field(res);

                // Populate the representation vector.
                repr[COL_INDEX_OPERAND_A] = op_a;
                repr[COL_INDEX_FLAG_A] = flag_a;
                repr[COL_INDEX_OPERAND_B] = op_b;
                repr[COL_INDEX_FLAG_B] = flag_b;
                repr[COL_INDEX_OPERAND_C] = op_c;
                repr[COL_INDEX_FLAG_C] = flag_c;
            }
            Self::Deref(DerefInstruction {
                shift_0,
                shift_1,
                res,
            }) => {
                // Set the DEREF opcode flag.
                repr[COL_INDEX_DEREF] = F::ONE;
                // The first-level pointer is always a memory access from `fp + shift_0`.
                repr[COL_INDEX_OPERAND_A] = F::from_usize(*shift_0);
                repr[COL_INDEX_FLAG_A] = F::ZERO;
                // The second-level offset is always an immediate value.
                repr[COL_INDEX_OPERAND_C] = F::from_usize(*shift_1);
                repr[COL_INDEX_FLAG_C] = F::ONE;

                // Handle the different types of the result operand `res`.
                match res {
                    MemOrFpOrConstant::Constant(c) => {
                        repr[COL_INDEX_OPERAND_B] = *c;
                        repr[COL_INDEX_FLAG_B] = F::ONE;
                        repr[COL_INDEX_AUX] = F::ONE;
                    }
                    MemOrFpOrConstant::MemoryAfterFp { offset } => {
                        repr[COL_INDEX_OPERAND_B] = F::from_usize(*offset);
                        repr[COL_INDEX_FLAG_B] = F::ZERO;
                        repr[COL_INDEX_AUX] = F::ONE;
                    }
                    MemOrFpOrConstant::Fp => {
                        repr[COL_INDEX_AUX] = F::ZERO;
                    }
                }
            }
            Self::JumpIfNotZero(JumpIfNotZeroInstruction {
                condition,
                dest,
                updated_fp,
            }) => {
                // Set the JUZ opcode flag.
                repr[COL_INDEX_JUZ] = F::ONE;
                // Convert operands to their field and flag representations.
                let (op_a, flag_a) = op_to_field(condition);
                let (op_b, flag_b) = op_to_field_fp(updated_fp);
                let (op_c, flag_c) = op_to_field(dest);

                // Populate the representation vector.
                repr[COL_INDEX_OPERAND_A] = op_a;
                repr[COL_INDEX_FLAG_A] = flag_a;
                repr[COL_INDEX_OPERAND_B] = op_b;
                repr[COL_INDEX_FLAG_B] = flag_b;
                repr[COL_INDEX_OPERAND_C] = op_c;
                repr[COL_INDEX_FLAG_C] = flag_c;
            }
            // Precompiles do not set flags in the main instruction columns.
            _ => {}
        }
        repr
    }
}

/// Helper to convert a `MemOrConstant` operand into its (value, flag) pair.
fn op_to_field(op: &MemOrConstant) -> (F, F) {
    match op {
        MemOrConstant::Constant(c) => (*c, F::ONE),
        MemOrConstant::MemoryAfterFp { offset } => (F::from_usize(*offset), F::ZERO),
    }
}

/// Helper to convert a `MemOrFp` operand into its (value, flag) pair.
fn op_to_field_fp(op: &MemOrFp) -> (F, F) {
    match op {
        MemOrFp::Fp => (F::ZERO, F::ONE), // Represents the `fp` register itself.
        MemOrFp::MemoryAfterFp { offset } => (F::from_usize(*offset), F::ZERO),
    }
}
