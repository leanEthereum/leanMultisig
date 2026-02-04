use crate::Table;

/// Large field = extension field of degree DIMENSION over koala-bear
pub const DIMENSION: usize = 5;

pub const DIGEST_LEN: usize = 8;

/// Minimum and maximum memory size (as powers of two)
pub const MIN_LOG_MEMORY_SIZE: usize = 16;
pub const MAX_LOG_MEMORY_SIZE: usize = 29;

/// Maximum memory size for VM runner (specific to this implementation)
pub const MAX_RUNNER_MEMORY_SIZE: usize = 1 << 24;

/// Minimum and maximum number of rows per table (as powers of two), both inclusive
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8; // Zero padding will be added to each at least, if this minimum is not reached, (ensuring AIR / GKR work fine, with SIMD, without too much edge cases). Long term, we should find a more elegant solution.
pub const MAX_LOG_N_ROWS_PER_TABLE: [(Table, usize); 3] = [
    (Table::execution(), 29),   // 3 lookups
    (Table::dot_product(), 25), // 4 lookups
    (Table::poseidon16(), 25),  // 4 lookups
]; // No overflow in logup: (TODO triple check) 3.2^29 + 4.2^25 + 4.2^25 < p = 2^31 - 2^24 + 1

/// Starting program counter
pub const STARTING_PC: usize = 1;

/// Ending program counter (the final block is a looping block of 1 instruction)
pub const ENDING_PC: usize = 0;

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
/// [reserved_area] = [00000000] [00000000] [10000000] [10000] [01000] [00100] [00010] [00001] [poseidon_16(0) (8 field elements)] [private input start pointer]
///
/// Convention: pointing to 16 zeros
pub const ZERO_VEC_PTR: usize = 0;

/// Convention: pointing to [10000000]
pub const SAMPLING_DOMAIN_SEPARATOR_PTR: usize = ZERO_VEC_PTR + 2 * DIGEST_LEN;

/// Convention: pointing to [10000] [01000] [00100] [00010] [00001]
pub const EXTENSION_BASIS_PTR: usize = SAMPLING_DOMAIN_SEPARATOR_PTR + DIGEST_LEN;

/// Convention: pointing to the 8 elements of poseidon_16(0)
pub const POSEIDON_16_NULL_HASH_PTR: usize = EXTENSION_BASIS_PTR + DIMENSION.pow(2);

/// Normal pointer to start of program input
pub const NONRESERVED_PROGRAM_INPUT_START: usize = (POSEIDON_16_NULL_HASH_PTR + DIGEST_LEN).next_multiple_of(DIMENSION);

/// The first element of basis corresponds to one
pub const ONE_VEC_PTR: usize = EXTENSION_BASIS_PTR;
