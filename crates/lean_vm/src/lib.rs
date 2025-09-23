use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_symmetric::Permutation;

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
use utils::{get_poseidon16, get_poseidon24};

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
pub struct WitnessDotProduct {
    pub cycle: usize,
    pub addr_0: usize,   // normal pointer
    pub addr_1: usize,   // normal pointer
    pub addr_res: usize, // normal pointer
    pub len: usize,
    pub slice_0: Vec<EF>,
    pub slice_1: Vec<EF>,
    pub res: EF,
}
impl WitnessDotProduct {
    pub fn addresses_and_len_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_0),
            F::from_usize(self.addr_1),
            F::from_usize(self.addr_res),
            F::from_usize(self.len),
        ]
    }
}

#[derive(Debug)]
pub struct RowMultilinearEval {
    pub addr_coeffs: usize,
    pub addr_point: usize,
    pub addr_res: usize,
    pub point: Vec<EF>,
    pub res: EF,
}

impl RowMultilinearEval {
    pub fn n_vars(&self) -> usize {
        self.point.len()
    }

    pub fn addresses_and_n_vars_field_repr(&self) -> [F; 4] {
        [
            F::from_usize(self.addr_coeffs),
            F::from_usize(self.addr_point),
            F::from_usize(self.addr_res),
            F::from_usize(self.n_vars()),
        ]
    }
}

#[derive(Debug, derive_more::Deref)]
pub struct WitnessMultilinearEval {
    pub cycle: usize,
    #[deref]
    pub inner: RowMultilinearEval,
}

#[derive(Debug, Clone)]
pub struct WitnessPoseidon16 {
    pub cycle: Option<usize>,
    pub addr_input_a: usize, // vectorized pointer (size 1)
    pub addr_input_b: usize, // vectorized pointer (size 1)
    pub addr_output: usize,  // vectorized pointer (size 2)
    pub input: [F; 16],
    pub output: [F; 16],
}

impl WitnessPoseidon16 {
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: get_poseidon16().permute([F::ZERO; 16]),
        }
    }

    pub fn addresses_field_repr(&self) -> [F; 3] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
        ]
    }
}

#[derive(Debug, Clone)]
pub struct WitnessPoseidon24 {
    pub cycle: Option<usize>,
    pub addr_input_a: usize, // vectorized pointer (size 2)
    pub addr_input_b: usize, // vectorized pointer (size 1)
    pub addr_output: usize,  // vectorized pointer (size 1)
    pub input: [F; 24],
    pub output: [F; 8], // last 8 elements of the output
}

impl WitnessPoseidon24 {
    pub fn poseidon_of_zero() -> Self {
        Self {
            cycle: None,
            addr_input_a: ZERO_VEC_PTR,
            addr_input_b: ZERO_VEC_PTR,
            addr_output: POSEIDON_24_NULL_HASH_PTR,
            input: [F::ZERO; 24],
            output: get_poseidon24().permute([F::ZERO; 24])[16..24]
                .try_into()
                .unwrap(),
        }
    }

    pub fn addresses_field_repr(&self) -> [F; 3] {
        [
            F::from_usize(self.addr_input_a),
            F::from_usize(self.addr_input_b),
            F::from_usize(self.addr_output),
        ]
    }
}
