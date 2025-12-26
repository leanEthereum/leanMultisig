/// Vector dimension for field operations
pub const DIMENSION: usize = 5;
/// Logarithm of vector length
pub const LOG_VECTOR_LEN: usize = 3;

/// Vector length (2^LOG_VECTOR_LEN)
pub const VECTOR_LEN: usize = 1 << LOG_VECTOR_LEN;

/// Maximum memory size for VM runner
pub const MAX_RUNNER_MEMORY_SIZE: usize = 1 << 24;

/// Starting program counter
pub const STARTING_PC: usize = 1;

/// Ending program counter (the final block is a looping block of 1 instruction)
pub const ENDING_PC: usize = 0;

/// See section 5 of https://eprint.iacr.org/2024/108.pdf
pub const UNIVARIATE_SKIPS: usize = 3;

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
pub const ONE_VEC_PTR: usize = 2 * VECTOR_LEN;

/// Convention: vectorized pointer of size 2, = the 16 elements of poseidon_16(0)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 3 * VECTOR_LEN;

/// 2^UNIVARIATE_SKIPS univariate polynomials, each of degree 2^UNIVARIATE_SKIPS - 1
/// The i-th polynomial defined by P(j) = 0 if i != j, P(i) = 1 (for i, j in [0, 2^UNIVARIATE_SKIPS))
pub const UNIVARIATE_SELECTORS_PTR: usize = POSEIDON_16_NULL_HASH_PTR + 2 * VECTOR_LEN;

/// Normal pointer to start of program input
pub const NONRESERVED_PROGRAM_INPUT_START: usize = 6 * VECTOR_LEN + (1_usize << UNIVARIATE_SKIPS).pow(2);
