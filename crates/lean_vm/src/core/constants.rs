/// Vector dimension for field operations
pub const DIMENSION: usize = 5;

/// Logarithm of vector length
pub const LOG_VECTOR_LEN: usize = 3;

/// Vector length (2^LOG_VECTOR_LEN)
pub const VECTOR_LEN: usize = 1 << LOG_VECTOR_LEN;

/// Convention: vectorized pointer of size 2, pointing to 16 zeros
pub const ZERO_VEC_PTR: usize = 0;

/// Convention: vectorized pointer of size 1, pointing to 10000000
pub const ONE_VEC_PTR: usize = 2;

/// Convention: vectorized pointer of size 2, = the 16 elements of poseidon_16(0)
pub const POSEIDON_16_NULL_HASH_PTR: usize = 3;

/// Convention: vectorized pointer of size 1, = the last 8 elements of poseidon_24(0)
pub const POSEIDON_24_NULL_HASH_PTR: usize = 5;

/// Normal pointer to start of public input
pub const PUBLIC_INPUT_START: usize = 6 * 8;

/// Maximum memory size for VM runner
pub const MAX_RUNNER_MEMORY_SIZE: usize = 1 << 24;
