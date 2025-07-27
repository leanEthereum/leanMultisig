use std::collections::BTreeMap;

type Label = String;

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

/// Represents a value that can either be a constant or a value from memory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrConstant<F> {
    /// A constant value (a field element).
    Constant(F),
    /// A memory location specified by a positive offset from the frame pointer (`fp`).
    ///
    /// Represents the scalar value at `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        shift: usize,
    },
}

/// Represents a value that can be a memory location, the `fp` register itself, or a constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant<F> {
    /// A memory location specified by a positive offset from `fp`. Represents `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        shift: usize,
    },
    /// The value of the frame pointer (`fp`) register itself.
    Fp,
    /// A constant value (a field element).
    Constant(F),
}

/// Represents a value that is either a memory location or the `fp` register itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFp {
    /// A memory location specified by a positive offset from `fp`. Represents `m[fp + shift]`.
    MemoryAfterFp {
        /// The offset from `fp` where the memory location is located.
        shift: usize,
    },
    /// The value of the frame pointer (`fp`) register itself.
    Fp,
}

/// The basic arithmetic operations supported by the VM's `Computation` instruction.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    /// Field addition in the base field.
    Add,
    /// Field multiplication in the base field.
    Mul,
}

/// Defines the instruction set for this zkVM, specialized for the `AggregateMerge` logic.
///
/// The ISA is minimal and includes basic arithmetic, memory operations, control flow,
/// and powerful precompiles for hashing and extension field arithmetic.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction<F> {
    /// Performs a basic arithmetic computation: `res = arg_a op arg_b`.
    ///
    /// This corresponds to the `ADD` and `MUL` opcodes in the design document.
    Computation {
        /// The arithmetic operation to perform (`Add` or `Mul`).
        operation: Operation,
        /// The first operand of the computation.
        arg_a: MemOrConstant<F>,
        /// The second operand of the computation.
        arg_b: MemOrFp,
        /// The memory location or constant that the result must be equal to.
        res: MemOrConstant<F>,
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
        res: MemOrFpOrConstant<F>,
    },
    /// A conditional jump, called `JUZ` (Jump Unless Zero)
    /// .
    /// Changes the `pc` if `condition` is non-zero.
    JumpIfNotZero {
        /// The value to check. The jump is taken if this value is not zero.
        condition: MemOrConstant<F>,
        /// The destination `pc` for the jump.
        dest: MemOrConstant<F>,
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

/// Hints are special instructions for the prover to resolve non-determinism.
///
/// They are not part of the verified computation trace.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hint<F> {
    /// A hint for the prover to allocate a new memory segment for a function's stack frame.
    ///
    /// This is the core mechanism for memory management in a VM without an `ap` (allocation pointer)
    /// register. The compiler pre-calculates the required memory size for each function.
    RequestMemory {
        /// The offset from `fp` where the pointer to the newly allocated segment will be stored.
        offset: usize,
        /// The requested size of the memory segment in scalar field elements.
        size: MemOrConstant<F>,
        /// If true, the start of the allocated memory is aligned to an 8-element boundary
        /// to facilitate vectorized memory access for extension field operations.
        /// The value stored at `m[fp + offset]` will be the aligned address divided by 8.
        vectorized: bool,
    },
    /// A hint for the prover to compute the bit decomposition of a base field element.
    ///
    /// This is a non-deterministic operation used for operations like range checks
    /// or other logic required by the XMSS signature scheme.
    DecomposeBits {
        /// The starting offset from `fp` where the resulting bits will be stored.
        res_offset: usize,
        /// The field element that needs to be decomposed into its bits.
        to_decompose: MemOrConstant<F>,
    },
    /// A hint used for debugging to print values from memory during execution.
    Print {
        /// A string containing line information (e.g., file and line number) for context.
        line_info: String,
        /// A list of memory locations or constants whose values should be printed.
        content: Vec<MemOrConstant<F>>,
    },
}
