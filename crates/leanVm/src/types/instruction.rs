use std::collections::BTreeMap;

type Label = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode<F> {
    pub instructions: Vec<Instruction<F>>,
    pub hints: BTreeMap<usize, Vec<Hint<F>>>, // pc -> hints
    pub public_input_start: usize,
    pub ending_pc: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrConstant<F> {
    Constant(F),
    MemoryAfterFp { shift: usize }, // m[fp + shift]
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFpOrConstant<F> {
    MemoryAfterFp { shift: usize }, // m[fp + shift]
    Fp,
    Constant(F),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MemOrFp {
    MemoryAfterFp { shift: usize }, // m[fp + shift]
    Fp,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Operation {
    Add,
    Mul,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Instruction<F> {
    Computation {
        operation: Operation,
        arg_a: MemOrConstant<F>,
        arg_b: MemOrFp,
        res: MemOrConstant<F>,
    },
    Deref {
        shift_0: usize,
        shift_1: usize,
        res: MemOrFpOrConstant<F>,
    }, // res = m[m[fp + shift_0] + shift_1]
    JumpIfNotZero {
        condition: MemOrConstant<F>,
        dest: MemOrConstant<F>,
        updated_fp: MemOrFp,
    },
    Poseidon2_16 {
        shift: usize,
    }, /*
        Read 4 vectorized pointers from stack:
        Poseidon2(m[8 * m[fp + shift]] .. 8 * (1 + m[fp + shift])] | m[8 * m[fp + shift + 1]] .. 8 * (1 + m[fp + shift + 1])])
        = m[8 * m[fp + shift + 2]] .. 8 * (1 + m[fp + shift + 2])] | m[8 * m[fp + shift + 3]] .. 8 * (1 + m[fp + shift + 3])]
       */
    Poseidon2_24 {
        shift: usize,
    }, // same as above, but with 24 field elements
    ExtensionMul {
        args: [usize; 3], // offset after fp
    },
}

/// Hints does not appear in the verified bytecode, but are useful during execution
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Hint<F> {
    RequestMemory {
        offset: usize, // the pointer to the allocated memory range will be stored at m[fp + offset]
        size: MemOrConstant<F>,
        /// if vectorized == true, the start of the allocated memory will be aligned to 8 field elements
        /// m[8X...] and we set m[fp + offset] = X
        vectorized: bool,
    },
    DecomposeBits {
        res_offset: usize, // m[fp + res_offset..fp + res_offset + 31] will contain the decomposed bits
        to_decompose: MemOrConstant<F>,
    },
    // Debug purpose
    Print {
        line_info: String,
        content: Vec<MemOrConstant<F>>,
    },
}
