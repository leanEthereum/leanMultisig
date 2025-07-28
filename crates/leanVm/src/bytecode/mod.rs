use std::collections::BTreeMap;

use hint::Hint;
use instruction::Instruction;

pub mod hint;
pub mod instruction;
pub mod operand;
pub mod operation;

/// Represents the compiled bytecode of a program for the zkVM.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode<F> {
    /// A vector of instructions that form the executable part of the program.
    ///
    /// The Program Counter (pc) iterates over this vector.
    pub instructions: Vec<Instruction<F>>,

    /// A map from a program counter (pc) value to a list of `Hint`s.
    ///
    /// Hints are auxiliary, non-deterministic instructions executed only by the prover.
    ///
    /// In this zkVM, they are crucial for managing memory allocations in the absence
    /// of an `ap` register.
    pub hints: BTreeMap<usize, Vec<Hint<F>>>,

    /// The memory offset from the frame pointer (fp) where the public input for the program begins.
    pub public_input_start: usize,

    /// The program counter (pc) value at which the program execution is considered complete.
    pub ending_pc: usize,
}
