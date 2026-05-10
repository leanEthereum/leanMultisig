use backend::*;
use lean_vm::{EF, F};

/// One logical sub-table inside a fancy-jagged commitment.
///
/// All columns of the sub-table share the same height. The width is required
/// to be a power of two; tables with non-power-of-two widths are decomposed
/// into a list of these by [`decompose_table_widths`].
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct SubTable {
    /// Log of the column width: this sub-table holds `1 << log_width` columns.
    pub log_width: usize,
    /// Number of (non-padded) rows. May be any positive integer.
    pub height: usize,
}

impl SubTable {
    pub const fn area(&self) -> usize {
        self.height << self.log_width
    }
}

/// Configuration of a fancy-jagged commitment: an ordered list of sub-tables
/// plus the derived bit-widths and area-prefix-sums needed by both prover and
/// verifier.
#[derive(Clone, Debug)]
pub struct JaggedConfig {
    pub sub_tables: Vec<SubTable>,
    /// `k`: bits to address a sub-table. = ceil(log2(sub_tables.len())).
    pub log_n_sub_tables: usize,
    /// `n`: bits to address a row. = ceil(log2(max height)).
    pub log_max_rows: usize,
    /// `c`: bits to address a column inside a sub-table. = max(log_width).
    pub log_max_cols: usize,
    /// `m`: log of the dense-polynomial size. = ceil(log2(sum of areas)).
    pub log_dense_size: usize,
    /// Cumulative areas: `cumulative_areas[y] = sum_{y' < y} 2^{c_{y'}} * h_{y'}`.
    /// Length = `sub_tables.len() + 1`. Sent to the verifier in the clear.
    pub cumulative_areas: Vec<usize>,
}

impl JaggedConfig {
    pub fn new(sub_tables: Vec<SubTable>) -> Self {
        assert!(!sub_tables.is_empty(), "JaggedConfig needs at least one sub-table");
        for st in &sub_tables {
            assert!(st.height > 0, "sub-table height must be positive");
        }

        let log_n_sub_tables = log2_ceil_usize(sub_tables.len().max(1));
        let log_max_rows = log2_ceil_usize(sub_tables.iter().map(|st| st.height).max().unwrap().max(1));
        let log_max_cols = sub_tables.iter().map(|st| st.log_width).max().unwrap();

        let mut cumulative_areas = Vec::with_capacity(sub_tables.len() + 1);
        let mut acc = 0usize;
        cumulative_areas.push(0);
        for st in &sub_tables {
            acc = acc.checked_add(st.area()).expect("dense size overflow");
            cumulative_areas.push(acc);
        }
        let log_dense_size = log2_ceil_usize(acc.max(1));

        Self {
            sub_tables,
            log_n_sub_tables,
            log_max_rows,
            log_max_cols,
            log_dense_size,
            cumulative_areas,
        }
    }

    pub fn n_sub_tables(&self) -> usize {
        self.sub_tables.len()
    }

    pub fn dense_size(&self) -> usize {
        1 << self.log_dense_size
    }

    pub fn total_area(&self) -> usize {
        *self.cumulative_areas.last().unwrap()
    }
}

/// Decompose a table of `width` columns into a sequence of power-of-two
/// sub-table widths whose sum equals `width`. We greedily peel off the
/// largest power of two that fits, which gives at most `ceil(log2(width)) + 1`
/// sub-tables (e.g. 30 -> 16 + 8 + 4 + 2).
pub fn decompose_table_widths(width: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut remaining = width;
    while remaining > 0 {
        let log =
            log2_strict_usize(remaining.next_power_of_two()).saturating_sub(usize::from(!remaining.is_power_of_two()));
        let chunk = 1usize << log;
        out.push(chunk);
        remaining -= chunk;
    }
    out
}

/// Build a [`JaggedConfig`] for a list of (height, width) tables, decomposing
/// each table's width into a sequence of power-of-two sub-tables.
///
/// The order of sub-tables in the returned config is "sub-tables of table 0
/// from largest width to smallest, then sub-tables of table 1, ...". The
/// returned `column_offsets[i]` gives, for each input table `i`, the start
/// index of its first sub-table in `config.sub_tables`.
pub fn build_jagged_config(tables: &[(usize, usize)]) -> (JaggedConfig, Vec<usize>) {
    let mut sub_tables = Vec::new();
    let mut column_offsets = Vec::with_capacity(tables.len());
    for &(height, width) in tables {
        column_offsets.push(sub_tables.len());
        for w in decompose_table_widths(width) {
            sub_tables.push(SubTable {
                log_width: log2_strict_usize(w),
                height,
            });
        }
    }
    (JaggedConfig::new(sub_tables), column_offsets)
}

/// Build the dense polynomial `q : {0,1}^m -> F` from per-sub-table column
/// data, using the row-major layout required by fancy jagged:
///
/// ```text
/// q[t_y + row * 2^{c_y} + col] = sub_tables[y].column(col)[row]
/// ```
///
/// `columns[y][col][row]` is expected to give the value at sub-table `y`,
/// logical column `col` (in `[0, 2^{c_y})`), row `row` (in `[0, h_y)`).
/// Padding past the cumulative area is filled with zero.
pub fn pack_dense(config: &JaggedConfig, columns: &[Vec<&[F]>]) -> Vec<F> {
    assert_eq!(columns.len(), config.n_sub_tables());
    let mut dense = F::zero_vec(config.dense_size());
    for (y, st) in config.sub_tables.iter().enumerate() {
        let width = 1usize << st.log_width;
        assert_eq!(
            columns[y].len(),
            width,
            "sub-table {y} expects {width} columns, got {}",
            columns[y].len()
        );
        let base = config.cumulative_areas[y];
        for (col, col_data) in columns[y].iter().enumerate() {
            assert_eq!(
                col_data.len(),
                st.height,
                "sub-table {y} column {col}: expected {} elements, got {}",
                st.height,
                col_data.len()
            );
            for (row, value) in col_data.iter().enumerate() {
                dense[base + row * width + col] = *value;
            }
        }
    }
    dense
}

/// Encode a usize into the big-endian boolean point of length `n_bits` over EF
/// (high bits at the front). Used to translate (sub_table_id, col_in_subtable)
/// into the `z_tab` / `z_col` evaluation points.
pub fn usize_to_point(value: usize, n_bits: usize) -> MultilinearPoint<EF> {
    assert!(value < 1 << n_bits || n_bits == 0);
    let mut point = Vec::with_capacity(n_bits);
    for i in (0..n_bits).rev() {
        let bit = (value >> i) & 1;
        point.push(if bit == 1 { EF::ONE } else { EF::ZERO });
    }
    MultilinearPoint(point)
}

/// Encode a usize into a vector of base-field elements (one bit per element,
/// big-endian, high bit first). Used for the cumulative_areas data sent to
/// the verifier.
pub fn usize_to_bits(value: usize, n_bits: usize) -> Vec<F> {
    assert!(value < 1 << n_bits || n_bits == 0);
    let mut out = Vec::with_capacity(n_bits);
    for i in (0..n_bits).rev() {
        let bit = (value >> i) & 1;
        out.push(if bit == 1 { F::ONE } else { F::ZERO });
    }
    out
}
