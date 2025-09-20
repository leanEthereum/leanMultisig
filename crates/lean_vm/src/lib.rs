use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};

mod error;
mod lean_isa;
mod memory;
mod profiler;
mod runner;
mod stack_trace;
pub use error::*;
pub use lean_isa::*;
pub use memory::*;
pub use runner::*;

pub type LocationInSourceCode = usize;

pub const DIMENSION: usize = 5;
pub const LOG_VECTOR_LEN: usize = 3;
pub const VECTOR_LEN: usize = 1 << LOG_VECTOR_LEN;
pub type F = KoalaBear;
pub type EF = QuinticExtensionFieldKB;

pub const ZERO_VEC_PTR: usize = 0; // convention (vectorized pointer of size 2, pointing to 16 zeros)
pub const ONE_VEC_PTR: usize = 2; // convention (vectorized pointer of size 1, pointing to 10000000)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 3; // convention (vectorized pointer of size 2, = the 16 elements of poseidon_16(0))
pub const POSEIDON_24_NULL_HASH_PTR: usize = 5; // convention (vectorized pointer of size 1, = the last 8 elements of poseidon_24(0))
pub const PUBLIC_INPUT_START: usize = 6 * 8; // normal pointer

// VM-side events collected during final execution only.
// These events are designed to be self-contained (store values),
// allowing zk_vm_trace to construct Witness* without rescanning memory.

#[derive(Debug, Clone)]
pub struct VmDotProductEvent {
    pub cycle: usize,
    pub addr_0: usize,   // normal pointer
    pub addr_1: usize,   // normal pointer
    pub addr_res: usize, // normal pointer
    pub len: usize,
    pub slice_0: Vec<EF>,
    pub slice_1: Vec<EF>,
    pub res: EF,
}

#[derive(Debug, Clone)]
pub struct VmMultilinearEvalEvent {
    pub cycle: usize,
    pub addr_coeffs: usize, // vectorized pointer, of size 8*2^n_vars
    pub addr_point: usize,  // vectorized pointer, of size n_vars
    pub addr_res: usize,    // vectorized pointer
    pub n_vars: usize,
    pub point: Vec<EF>,
    pub res: EF,
}

#[derive(Debug, Clone)]
pub struct VmPoseidon16Event {
    pub cycle: usize,
    pub addr_input_a: usize, // vectorized pointer (size 1)
    pub addr_input_b: usize, // vectorized pointer (size 1)
    pub addr_output: usize,  // vectorized pointer (size 2)
    pub input: [F; 16],
    pub output: [F; 16],
}

#[derive(Debug, Clone)]
pub struct VmPoseidon24Event {
    pub cycle: usize,
    pub addr_input_a: usize, // vectorized pointer (size 2)
    pub addr_input_b: usize, // vectorized pointer (size 1)
    pub addr_output: usize,  // vectorized pointer (size 1)
    pub input: [F; 24],
    pub output: [F; 8], // last 8 elements of the output
}
