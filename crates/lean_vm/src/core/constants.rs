use multilinear_toolkit::prelude::PrimeCharacteristicRing;
use num_enum::TryFromPrimitive;
use strum_macros::EnumIter;

use crate::{
    DotProductPrecompile, F, Memory, ModularPrecompile, Poseidon16Precompile, Poseidon24Precompile, PrecompileExecutionContext, PrecompileTrace, RunnerError
};

/// Vector dimension for field operations
pub const DIMENSION: usize = 5;

/// Logarithm of vector length
pub const LOG_VECTOR_LEN: usize = 3;

/// Vector length (2^LOG_VECTOR_LEN)
pub const VECTOR_LEN: usize = 1 << LOG_VECTOR_LEN;

/// Maximum memory size for VM runner
pub const MAX_RUNNER_MEMORY_SIZE: usize = 1 << 24;

/// Memory layout:
///
/// [memory] = [public_data] [private_data]
///       
/// public_data: shared between prover and verifier
/// private_data: witness, committed by the prover
///
/// [public_data] = [reserved_area] [program_input]
///
/// reserved_area: reserved for special constants (size = 48 field elements)
/// program_input: the input of the program we want to prove
///
/// [reserved_area] = [00000000] [00000000] [10000000] [poseidon_16(0) (16 field elements)] [poseidon_24(0) (8 last field elements)]
///
/// Convention: vectorized pointer of size 2, pointing to 16 zeros
pub const ZERO_VEC_PTR: usize = 0;

/// Convention: vectorized pointer of size 1, pointing to 10000000
pub const ONE_VEC_PTR: usize = 2;

/// Convention: vectorized pointer of size 2, = the 16 elements of poseidon_16(0)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 3;

/// Convention: vectorized pointer of size 1, = the last 8 elements of poseidon_24(0)
pub const POSEIDON_24_NULL_HASH_PTR: usize = 5;

/// Normal pointer to start of program input
pub const NONRESERVED_PROGRAM_INPUT_START: usize = 6 * 8;

#[derive(Clone, Copy, Debug, PartialEq, Eq, TryFromPrimitive, PartialOrd, Ord, Hash, EnumIter)]
#[repr(usize)]
pub enum Table {
    _UNUSED,
    Poseidon16,
    Poseidon24,
    DotProduct,
    MultilinearEval,
}

impl Table {
    pub fn embed<PF: PrimeCharacteristicRing>(&self) -> PF {
        PF::from_usize(*self as usize)
    }

    pub fn name(&self) -> &'static str {
        match self {
            Table::_UNUSED => "u_n_u_s_e_d",
            Table::Poseidon16 => "poseidon16",
            Table::Poseidon24 => "poseidon24",
            Table::DotProduct => "dot_product",
            Table::MultilinearEval => "multilinear_eval",
        }
    }
}

impl Table {
    #[inline(always)]
    pub fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        aux: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        precompile_execution_context: PrecompileExecutionContext<'_>,
    ) -> Result<(), RunnerError> {
        match self {
            Self::_UNUSED | Self::MultilinearEval => {
                unreachable!()
            }
            Self::DotProduct => DotProductPrecompile::execute(
                arg_a,
                arg_b,
                arg_c,
                aux,
                memory,
                trace,
                precompile_execution_context,
            ),
            Self::Poseidon16 => Poseidon16Precompile::execute(
                arg_a,
                arg_b,
                arg_c,
                aux,
                memory,
                trace,
                precompile_execution_context,
            ),
            Self::Poseidon24 => Poseidon24Precompile::execute(
                arg_a,
                arg_b,
                arg_c,
                aux,
                memory,
                trace,
                precompile_execution_context,
            ),
        }
    }
}
