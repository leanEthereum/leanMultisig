use crate::Table;

/// Domain separation in logup
pub const LOGUP_MEMORY_DOMAINSEP: usize = 0;
pub const LOGUP_PRECOMPILE_DOMAINSEP: usize = 1;
pub const LOGUP_BYTECODE_DOMAINSEP: usize = 2;

/// Large field = extension field of degree DIMENSION over Goldilocks
pub const DIMENSION: usize = 3;

pub const DIGEST_LEN: usize = 4;

pub const MIN_WHIR_LOG_INV_RATE: usize = 1;
pub const MAX_WHIR_LOG_INV_RATE: usize = 4;

/// Minimum and maximum memory size (as powers of two)
pub const MIN_LOG_MEMORY_SIZE: usize = 16;
pub const MAX_LOG_MEMORY_SIZE: usize = 26;

pub const MIN_BYTECODE_LOG_SIZE: usize = 8;

/// Minimum and maximum number of rows per table (as powers of two), both inclusive
pub const MIN_LOG_N_ROWS_PER_TABLE: usize = 8; // Zero padding will be added to each at least, if this minimum is not reached, (ensuring AIR / GKR work fine, with SIMD, without too much edge cases). Long term, we should find a more elegant solution.
pub const MAX_LOG_N_ROWS_PER_TABLE: [(Table, usize); 3] = [
    (Table::execution(), 25),
    (Table::extension_op(), 21),
    (Table::poseidon8(), 21),
];

pub fn max_log_n_rows_per_table(table: &Table) -> usize {
    MAX_LOG_N_ROWS_PER_TABLE
        .iter()
        .find(|(t, _)| t == table)
        .map(|(_, m)| *m)
        .unwrap()
}

/// Starting program counter
pub const STARTING_PC: usize = 1;

/// Ending program counter (the final block is a looping block of 1 instruction)
pub const ENDING_PC: usize = 0;

#[cfg(test)]
mod tests {
    use backend::*;

    use crate::{F, MAX_LOG_MEMORY_SIZE, MAX_LOG_N_ROWS_PER_TABLE, Table, TableT};

    /// CRITICAL FOUR SOUNDNESS: TODO tripple check
    #[test]
    fn ensure_no_overflow_in_logup() {
        fn memory_lookups_count<T: TableT>(t: &T) -> usize {
            t.lookups().iter().map(|l| l.values.len()).sum::<usize>()
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
            max_surface += (table.n_columns() as u64) << (max_log_n_rows as u64);
        }
        assert!(max_surface <= 1 << 30); // Maximum data we can commit via WHIR using an initial folding factor of 7, and rate = 1/2
    }
}
