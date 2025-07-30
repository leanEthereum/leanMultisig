use super::{
    operand::{MemOrConstant, MemOrFp, MemOrFpOrConstant},
    operation::Operation,
};

/// Defines the instruction set for this zkVM, specialized for the `AggregateMerge` logic.
///
/// The ISA is minimal and includes basic arithmetic, memory operations, control flow,
/// and powerful precompiles for hashing and extension field arithmetic.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction {
    /// Performs a basic arithmetic computation: `res = arg_a op arg_b`.
    ///
    /// This corresponds to the `ADD` and `MUL` opcodes in the design document.
    Computation {
        /// The arithmetic operation to perform (`Add` or `Mul`).
        operation: Operation,
        /// The first operand of the computation.
        arg_a: MemOrConstant,
        /// The second operand of the computation.
        arg_b: MemOrFp,
        /// The memory location or constant that the result must be equal to.
        res: MemOrConstant,
    },
    /// Performs a memory dereference: `res = m[m[fp + shift_0] + shift_1]`.
    ///
    /// This corresponds to the `DEREF` opcode.
    Deref {
        /// The offset from `fp` for the first memory access, which yields a pointer.
        shift_0: usize,
        /// The offset added to the pointer from the first access to get the final address.
        shift_1: usize,
        /// The value that the result of the double dereference must be equal to.
        res: MemOrFpOrConstant,
    },
    /// A conditional jump, called `JUZ` (Jump Unless Zero).
    ///
    /// Changes the `pc` if `condition` is non-zero.
    JumpIfNotZero {
        /// The value to check. The jump is taken if this value is not zero.
        condition: MemOrConstant,
        /// The destination `pc` for the jump.
        dest: MemOrConstant,
        /// The new value for the frame pointer (`fp`) after the instruction.
        updated_fp: MemOrFp,
    },
    /// **Precompile** for a Poseidon2 permutation over 16 base field elements.
    ///
    /// This is used for hashing operations within the `AggregateMerge` algorithm.
    /// The precompile performs: `Poseidon2(m'[m[fp+s]], m'[m[fp+s+1]]) = (m'[m[fp+s+2]], m'[m[fp+s+3]])`,
    /// where:
    /// - `s` is the shift,
    /// - `m` is scalar memory,
    /// - `m'` is vectorized memory access (a chunk of 8 base field elements, representing a degree-8 extension field element).
    Poseidon2_16 {
        /// The starting offset `s` from `fp`. The instruction reads 4 pointers from `m[fp+s]` to `m[fp+s+3]`.
        shift: usize,
    },
    /// **Precompile** for a Poseidon2 permutation over 24 base field elements.
    ///
    /// This operates similarly to `Poseidon2_16` but on 3 concatenated input vectors and 3 output vectors.
    ///
    /// It reads 6 pointers from memory, starting at `m[fp+shift]`.
    Poseidon2_24 {
        /// The starting offset from `fp`. The instruction reads 6 pointers from `m[fp+shift]` to `m[fp+shift+5]`.
        shift: usize,
    },
    /// **Precompile** for multiplication in the degree-8 extension field.
    ///
    /// This is important for speeding up recursive proof verification (`snark_verify`).
    ExtensionMul {
        /// An array of three offsets from `fp`. These point to the start of the 8-cell memory blocks
        /// for the two input extension field elements and the resulting output element.
        args: [usize; 3],
    },
}
