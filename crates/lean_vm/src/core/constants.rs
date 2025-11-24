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

/// Precompiles Indexes
pub const TABLE_INDEX_POSEIDONS_16: usize = 1; // should be != 0
pub const TABLE_INDEX_POSEIDONS_24: usize = 2;
pub const TABLE_INDEX_DOT_PRODUCTS: usize = 3;
pub const TABLE_INDEX_MULTILINEAR_EVAL: usize = 4;
