use computation::ComputationInstruction;
use deref::DerefInstruction;
use dot_product::DotProductInstruction;
use jump::JumpIfNotZeroInstruction;
use multilinear_eval::MultilinearEvalInstruction;
use p3_symmetric::Permutation;
use poseidon16::Poseidon2_16Instruction;
use poseidon24::Poseidon2_24Instruction;

use crate::{
    constant::{DIMENSION, F},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::manager::MemoryManager,
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
}
