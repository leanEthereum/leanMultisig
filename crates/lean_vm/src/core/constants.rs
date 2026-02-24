use crate::Table;

/// Domain separation in logup
pub const LOGUP_MEMORY_DOMAINSEP: usize = 0;
pub const LOGUP_PRECOMPILE_DOMAINSEP: usize = 1;
pub const LOGUP_BYTECODE_DOMAINSEP: usize = 2;

/// Large field = extension field of degree DIMENSION over koala-bear
pub const DIMENSION: usize = 5;

pub const DIGEST_LEN: usize = 8;

pub const MIN_WHIR_LOG_INV_RATE: usize = 1;
pub const MAX_WHIR_LOG_INV_RATE: usize = 4;

/// Minimum and maximum memory size (as powers of two)
pub const MIN_LOG_MEMORY_SIZE: usize = 16;
pub const MAX_LOG_MEMORY_SIZE: usize = 26;

/// Minimum and maximum number of rows per table (as powers of two), both inclusive
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8; // Zero padding will be added to each at least, if this minimum is not reached, (ensuring AIR / GKR work fine, with SIMD, without too much edge cases). Long term, we should find a more elegant solution.
pub const MAX_LOG_N_ROWS_PER_TABLE: [(Table, usize); 3] = [
    (Table::execution(), 25),
    (Table::extension_op(), 20),
    (Table::poseidon16(), 21),
];

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
/// [reserved_area] = [00000000] [00000000] [10000000] [10000] [01000] [00100] [00010] [00001] [poseidon_16(0) (8 FE)] [111..111 (16 FE)] [2 -1 -1 1]
///
/// pointing to 16 zeros
pub const ZERO_VEC_PTR: usize = 0;

/// pointing to [10000000]
pub const SAMPLING_DOMAIN_SEPARATOR_PTR: usize = ZERO_VEC_PTR + 2 * DIGEST_LEN;

/// pointing to [10000] [01000] [00100] [00010] [00001]
pub const EXTENSION_BASIS_PTR: usize = SAMPLING_DOMAIN_SEPARATOR_PTR + DIGEST_LEN;

/// pointing to the 8 elements of poseidon_16(0)
pub const POSEIDON_16_NULL_HASH_PTR: usize = EXTENSION_BASIS_PTR + DIMENSION.pow(2);

/// POINTING TO 111..111 (`NUM_REPEATED_ONES_IN_RESERVED_MEMORY` times)
pub const NUM_REPEATED_ONES_IN_RESERVED_MEMORY: usize = 16;
pub const REPEATED_ONES_PTR: usize = POSEIDON_16_NULL_HASH_PTR + DIGEST_LEN;

/// [2, -1, -1, 1] is useful to compute (xy + (1-x)(1-y)) = 2xy - x - y + 1 = dot_product([xy, x, y, 1], [2, -1, -1, 1])
pub const EQ_MLE_COEFFS_LEN: usize = 4;
pub const EQ_MLE_COEFFS_PTR: usize = REPEATED_ONES_PTR + NUM_REPEATED_ONES_IN_RESERVED_MEMORY;

/// Normal pointer to start of program input
pub const NONRESERVED_PROGRAM_INPUT_START: usize = (EQ_MLE_COEFFS_PTR + EQ_MLE_COEFFS_LEN).next_multiple_of(DIMENSION);

/// The first element of basis corresponds to one
pub const ONE_EF_PTR: usize = EXTENSION_BASIS_PTR;

#[cfg(test)]
mod tests {
    use backend::*;

    use crate::{DIMENSION, F, MAX_LOG_MEMORY_SIZE, MAX_LOG_N_ROWS_PER_TABLE, Table, TableT};

    /// CRITICAL FOUR SOUNDNESS: TODO tripple check
    #[test]
    fn ensure_no_overflow_in_logup() {
        fn memory_lookups_count<T: TableT>(t: &T) -> usize {
            t.lookups_f().iter().map(|l| l.values.len()).sum::<usize>() + t.lookups_ef().len() * DIMENSION
        }
        // memory lookup
        let mut max_memory_logup_sum: u64 = 0;
        for (table, max_log_n_rows) in MAX_LOG_N_ROWS_PER_TABLE {
            let n_rows = 1 << max_log_n_rows;
            let num_lookups = memory_lookups_count(&table);
            max_memory_logup_sum += (num_lookups * n_rows) as u64;
            println!("Table {} has {} memory lookups", table.name(), num_lookups * n_rows);
        }
        assert!(max_memory_logup_sum < F::ORDER_U64);

        // bytecode lookup
        assert!(
            MAX_LOG_N_ROWS_PER_TABLE
                .iter()
                .find(|(table, _)| *table == Table::execution())
                .unwrap()
                .1
                < log2_ceil_u64(F::ORDER_U64) as usize
        );
    }

    #[test]
    fn ensure_not_too_big_commitment_surface() {
        let mut max_surface: u64 = 2 * (1 << MAX_LOG_MEMORY_SIZE) as u64; // memory and acc_memory
        for (table, max_log_n_rows) in MAX_LOG_N_ROWS_PER_TABLE {
            max_surface += (table.n_committed_columns() as u64) << (max_log_n_rows as u64);
        }
        assert!(max_surface <= 1 << 30); // Maximum data we can commit via WHIR using an initial folding factor of 7, and rate = 1/2
    }
}
