use backend::*;
use lean_vm::{
    ALL_TABLES, COL_PC, CommittedStatements, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE, N_INSTRUCTION_COLUMNS,
    STARTING_PC, sort_tables_by_height,
};
use lean_vm::{EF, F, Table, TableT, TableTrace};
use std::collections::BTreeMap;
use tracing::instrument;
use utils::VarCount;
use utils::ansi::Colorize;

/*
Stacking of various (multilinear) polynomials into a single -big- (multilinear) polynomial, which is committed via WHIR.

Memory is the first table in `ALL_TABLES`, has no AIR / no bus, and is always the
tallest (>= every other table's height). It is therefore always laid out first in
the stacked polynomial:

[------------------------------ Memory value -----------------------]
[------------------------ Memory acc (multiplicity) -----------------]
[------ Bytecode Accumulator -----]                             (padded to >= largest non-memory table)
[-------- Execution Col 0 --------]
[-------- Execution Col 1 --------]
...
[-------- Execution Col 19 -------]
[Dot-Product Col 0]
[Dot-Product Col 1]
...
[Dot-Product Col n]
[Poseidon-16 Col 0]
[Poseidon-16 Col 1]
...
[Poseidon-16 Col m]

(The order between Dot-Product and Poseidon-16 varies based on which table has more rows, but they are always after the execution table)
*/

#[derive(Debug)]
pub struct StackedPcsWitness {
    pub stacked_n_vars: VarCount,
    pub inner_witness: Witness<EF>,
    pub global_polynomial: MleOwned<EF>,
}

pub fn stacked_pcs_global_statements(
    stacked_n_vars: VarCount,
    bytecode_n_vars: VarCount,
    ending_pc: usize,
    previous_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);
    let max_other_table_n_vars = max_non_memory_height(&tables_heights_sorted);

    let mut global_statements = previous_statements;
    let mut offset = 0;

    for (table, n_vars) in &tables_heights_sorted {
        if table.is_execution_table() {
            // Important: ensure both initial and final PC conditions are correct
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + (COL_PC << n_vars),
                EF::from_usize(STARTING_PC),
            ));
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + ((COL_PC + 1) << n_vars) - 1,
                EF::from_usize(ending_pc),
            ));
        }
        for (point, eq_values, next_values) in &committed_statements[table] {
            if !next_values.is_empty() {
                global_statements.push(SparseStatement::new_next(
                    stacked_n_vars,
                    point.clone(),
                    next_values
                        .iter()
                        .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                        .collect(),
                ));
            }
            global_statements.push(SparseStatement::new(
                stacked_n_vars,
                point.clone(),
                eq_values
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
        offset += table.n_columns() << n_vars;
        // Right after the Memory table columns, bytecode_acc occupies its own slot,
        // padded to >= the largest non-memory table height.
        if *table == Table::memory() {
            offset += 1 << bytecode_n_vars.max(max_other_table_n_vars);
        }
    }
    global_statements
}

fn max_non_memory_height(sorted: &[(Table, VarCount)]) -> VarCount {
    sorted
        .iter()
        .filter(|(t, _)| *t != Table::memory())
        .map(|(_, h)| *h)
        .max()
        .unwrap()
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit(
    prover_state: &mut impl FSProver<EF>,
    whir_config_builder: &WhirConfigBuilder,
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> StackedPcsWitness {
    let tables_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);
    let log_memory = tables_heights[&Table::memory()];
    // Memory must be the tallest table.
    assert_eq!(tables_heights_sorted[0].0, Table::memory());
    // Memory must be at least as large as the execution table.
    assert!(log_memory >= tables_heights[&Table::execution()]);

    let stacked_n_vars = compute_stacked_n_vars(
        log2_strict_usize(bytecode_acc.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut global_polynomial = F::zero_vec(1 << stacked_n_vars); // TODO avoid cloning all witness data
    let mut offset = 0;
    let largest_non_memory_height = 1 << max_non_memory_height(&tables_heights_sorted);

    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index in 0..table.n_columns() {
            let col = &traces[table].columns[col_index];
            global_polynomial[offset..][..n_rows].copy_from_slice(&col[..n_rows]);
            offset += n_rows;
        }
        if *table == Table::memory() {
            // bytecode_acc is laid out right after the memory columns, padded with zeros to at
            // least the largest non-memory table height (`global_polynomial` is zero-initialized).
            global_polynomial[offset..][..bytecode_acc.len()].copy_from_slice(bytecode_acc);
            offset += largest_non_memory_height.max(bytecode_acc.len());
        }
    }
    assert_eq!(log2_ceil_usize(offset), stacked_n_vars);
    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            offset,
            stacked_n_vars - 1,
            (offset as f64) / (1 << (stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    let global_polynomial = MleOwned::Base(global_polynomial);

    let inner_witness =
        WhirConfig::new(whir_config_builder, stacked_n_vars).commit(prover_state, &global_polynomial, offset);
    StackedPcsWitness {
        stacked_n_vars,
        inner_witness,
        global_polynomial,
    }
}

pub fn stacked_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    let log_memory = tables_heights[&Table::memory()];
    let max_non_memory = tables_heights
        .iter()
        .filter(|(t, _)| **t != Table::memory())
        .map(|(_, h)| *h)
        .max()
        .unwrap();
    if log_memory < tables_heights[&Table::execution()] || log_memory < max_non_memory {
        // memory must be at least as large as the number of cycles
        // and the largest of all (non-memory) tables
        return Err(ProofError::InvalidProof);
    }

    let stacked_n_vars = compute_stacked_n_vars(log_bytecode, tables_heights);
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment(verifier_state)
}

fn compute_stacked_n_vars(log_bytecode: usize, tables_log_heights: &BTreeMap<Table, VarCount>) -> VarCount {
    let max_non_memory_height = tables_log_heights
        .iter()
        .filter(|(t, _)| **t != Table::memory())
        .map(|(_, h)| *h)
        .max()
        .unwrap();
    let total_len = (1 << log_bytecode.max(max_non_memory_height))
        + tables_log_heights
            .iter()
            .map(|(table, log_n_rows)| table.n_columns() << log_n_rows)
            .sum::<usize>();
    log2_ceil_usize(total_len)
}

pub fn min_stacked_n_vars(log_bytecode: usize) -> usize {
    let mut min_tables_log_heights = BTreeMap::new();
    for table in ALL_TABLES {
        let h = if table == Table::memory() {
            MIN_LOG_MEMORY_SIZE
        } else {
            MIN_LOG_N_ROWS_PER_TABLE
        };
        min_tables_log_heights.insert(table, h);
    }
    compute_stacked_n_vars(log_bytecode, &min_tables_log_heights)
}

pub fn total_whir_statements() -> usize {
    4 // public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            // AIR
            table.n_columns()
            + table.n_shift_columns()
            // Lookups into memory
            + table.lookups().iter().map(|lookup| 1 + lookup.values.len()).sum::<usize>()
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
}
