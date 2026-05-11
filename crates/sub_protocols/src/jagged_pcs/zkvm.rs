//! ZkVM-specific layer over the generic jagged PCS.
//!
//! Encapsulates the layout convention used by `lean_prover` to commit the
//! whole leanVM trace via a single jagged commitment:
//!
//! ```text
//! sub-table 0 : memory             (1 col,  height = 2^log_memory)
//! sub-table 1 : memory_acc         (1 col,  height = 2^log_memory)
//! sub-table 2 : bytecode_acc       (1 col,  height = 2^log_bytecode)
//! sub-tables 3..: per AIR table, decomposed into power-of-two-width chunks
//!                 (e.g. execution = 16 + 4 cols, height = non_padded_n_rows)
//! ```
//!
//! Memory / acc / bytecode_acc are already power-of-two and zero-padded, so
//! their `padding_value` is zero and `JaggedClaim::value` is just the raw
//! evaluation. AIR-table columns use `padding_value` from
//! `Table::padding_row(zero_vec_ptr, null_hash_ptr)`.
//!
//! Construction of the layout is identical on prover and verifier sides as
//! long as both agree on `(log_memory, log_bytecode, non_padded_n_rows[T])`.

use std::collections::BTreeMap;

use backend::*;
use lean_vm::{ALL_TABLES, EF, F, Table, TableT};

use super::config::{JaggedConfig, SubTable, decompose_table_widths};

/// Coordinate of one logical column inside the jagged commitment.
#[derive(Debug, Clone, Copy)]
pub struct ColumnLocation {
    pub sub_table_id: usize,
    pub col_in_sub_table: usize,
}

/// Layout of a leanVM jagged commitment: jagged config + per-table column index.
#[derive(Debug, Clone)]
pub struct ZkvmJaggedLayout {
    pub config: JaggedConfig,
    pub memory_st: usize,
    pub memory_acc_st: usize,
    pub bytecode_acc_st: usize,
    /// `table_columns[table][col_index_in_air]` gives the (sub_table, col)
    /// coordinates for that AIR column.
    pub table_columns: BTreeMap<Table, Vec<ColumnLocation>>,
}

impl ZkvmJaggedLayout {
    pub fn new(log_memory: usize, log_bytecode: usize, non_padded_per_table: &BTreeMap<Table, usize>) -> Self {
        let mut sub_tables = Vec::new();

        let memory_st = sub_tables.len();
        sub_tables.push(SubTable {
            log_width: 0,
            height: 1 << log_memory,
        });
        let memory_acc_st = sub_tables.len();
        sub_tables.push(SubTable {
            log_width: 0,
            height: 1 << log_memory,
        });
        let bytecode_acc_st = sub_tables.len();
        sub_tables.push(SubTable {
            log_width: 0,
            height: 1 << log_bytecode,
        });

        let mut table_columns: BTreeMap<Table, Vec<ColumnLocation>> = BTreeMap::new();
        for &table in &ALL_TABLES {
            let n_cols = table.n_columns();
            // h = 0 is legal for tables whose precompiles aren't used in
            // this run (e.g. extension_op when no extension-field op is
            // executed). The corresponding sub-tables contribute nothing to
            // the dense polynomial; the BP returns 0 and the padding
            // correction cancels the AIR sumcheck output, so the per-claim
            // contribution to v_combined is zero.
            let h = non_padded_per_table[&table];
            let widths = decompose_table_widths(n_cols);
            let mut col_locs = Vec::with_capacity(n_cols);
            let mut col_offset = 0;
            for w in widths {
                let st_id = sub_tables.len();
                sub_tables.push(SubTable {
                    log_width: log2_strict_usize(w),
                    height: h,
                });
                for c in 0..w {
                    col_locs.push(ColumnLocation {
                        sub_table_id: st_id,
                        col_in_sub_table: c,
                    });
                }
                col_offset += w;
            }
            assert_eq!(col_offset, n_cols);
            table_columns.insert(table, col_locs);
        }

        let config = JaggedConfig::new(sub_tables);
        Self {
            config,
            memory_st,
            memory_acc_st,
            bytecode_acc_st,
            table_columns,
        }
    }

    /// Look up where AIR column `col` of `table` lives in the jagged
    /// commitment.
    pub fn locate(&self, table: Table, col_index_in_air: usize) -> ColumnLocation {
        self.table_columns[&table][col_index_in_air]
    }
}

/// Compute the per-column padding values for an AIR table, indexed by the
/// table's AIR column index.
pub fn table_padding_values(table: Table, zero_vec_ptr: usize, null_hash_ptr: usize) -> Vec<F> {
    let row = table.padding_row(zero_vec_ptr, null_hash_ptr);
    row[..table.n_columns()].to_vec()
}

/// Pad a `MultilinearPoint` of length `L` to length `target_len >= L` by
/// prepending zeros (high-bit padding). Used to lift the public-memory
/// random point (length `log2(public_memory_size)`) up to a length-`log_memory`
/// row point that addresses the same data (the public input lives in the
/// first `public_memory_size` cells of memory).
pub fn pad_point_high(point: &MultilinearPoint<EF>, target_len: usize) -> MultilinearPoint<EF> {
    assert!(target_len >= point.len());
    let mut v = vec![EF::ZERO; target_len - point.len()];
    v.extend_from_slice(&point.0);
    MultilinearPoint(v)
}
