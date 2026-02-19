use lean_vm::{
    ALL_TABLES, COL_PC, CommittedStatements, DIMENSION, ENDING_PC, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE,
    N_INSTRUCTION_COLUMNS, STARTING_PC, sort_tables_by_height,
};
use lean_vm::{EF, F, Table, TableT, TableTrace};
use multilinear_toolkit::prelude::*;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::ansi::Colorize;
use utils::{VarCount, transpose_slice_to_basis_coefficients};

/*
Stacking of various (multilinear) polynomials into a single -big- (multilinear) polynomial, which is committed via WHIR.
[------------------------------ Memory ------------------------------]
[------------------------ Memory Accumulator ------------------------]
[------ Bytecode Accumulator -----]                             (padded to bas as least as large as the execution table)
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
    memory_n_vars: VarCount,
    bytecode_n_vars: VarCount,
    previous_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);

    let mut global_statements = previous_statements;
    let mut offset = 2 << memory_n_vars; // memory + memory_acc

    let max_table_n_vars = tables_heights_sorted[0].1;
    offset += 1 << bytecode_n_vars.max(max_table_n_vars); // bytecode acc

    for (table, n_vars) in tables_heights_sorted {
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
                EF::from_usize(ENDING_PC),
            ));
        }
        for (point, col_statements) in &committed_statements[&table] {
            global_statements.push(SparseStatement::new(
                stacked_n_vars,
                point.clone(),
                col_statements
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
        offset += table.n_committed_columns() << n_vars;
    }
    global_statements
}

#[instrument(skip_all)]
pub fn stack_polynomials_and_commit(
    prover_state: &mut impl FSProver<EF>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    memory_acc: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> StackedPcsWitness {
    assert_eq!(memory.len(), memory_acc.len());
    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);
    assert!(log2_strict_usize(memory.len()) >= tables_heights[&Table::execution()]); // memory must be at least as large as the number of cycles (TODO add some padding when this is not the case)
    assert!(tables_heights[&Table::execution()] >= tables_heights_sorted[0].1); // execution table must be the largest table (TODO add some padding when this is not the case)

    let stacked_n_vars = compute_stacked_n_vars(
        log2_strict_usize(memory.len()),
        log2_strict_usize(bytecode_acc.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut global_polynomial = F::zero_vec(1 << stacked_n_vars); // TODO avoid cloning all witness data
    global_polynomial[..memory.len()].copy_from_slice(memory);
    let mut offset = memory.len();
    global_polynomial[offset..][..memory_acc.len()].copy_from_slice(memory_acc);
    offset += memory_acc.len();

    global_polynomial[offset..][..bytecode_acc.len()].copy_from_slice(bytecode_acc);
    let largest_table_height = 1 << tables_heights_sorted[0].1;
    offset += largest_table_height.max(bytecode_acc.len()); // we may pad bytecode_acc to match largest table height

    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index_f in 0..table.n_columns_f_air() {
            let col = &traces[table].base[col_index_f];
            global_polynomial[offset..][..n_rows].copy_from_slice(&col[..n_rows]);
            offset += n_rows;
        }
        for col_index_ef in 0..table.n_columns_ef_air() {
            let col = &traces[table].ext[col_index_ef];
            let transposed = transpose_slice_to_basis_coefficients(col);
            for basis_col in transposed {
                global_polynomial[offset..][..n_rows].copy_from_slice(&basis_col);
                offset += n_rows;
            }
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
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    if log_memory < tables_heights[&Table::execution()]
        || tables_heights[&Table::execution()] < tables_heights.values().copied().max().unwrap()
    {
        // memory must be at least as large as the number of cycles
        // execution table must be the largest table
        return Err(ProofError::InvalidProof);
    }

    let stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode, tables_heights);
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment(verifier_state)
}

fn compute_stacked_n_vars(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> VarCount {
    let max_table_log_n_rows = tables_log_heights.values().copied().max().unwrap();
    let total_len = (2 << log_memory)
        + (1 << log_bytecode.max(max_table_log_n_rows))
        + tables_log_heights
            .iter()
            .map(|(table, log_n_rows)| table.n_committed_columns() << log_n_rows)
            .sum::<usize>();
    log2_ceil_usize(total_len)
}

pub fn min_stacked_n_vars(log_bytecode: usize) -> usize {
    let mut min_tables_log_heights = BTreeMap::new();
    for table in ALL_TABLES {
        min_tables_log_heights.insert(table, MIN_LOG_N_ROWS_PER_TABLE);
    }
    compute_stacked_n_vars(MIN_LOG_MEMORY_SIZE, log_bytecode, &min_tables_log_heights)
}

pub fn total_whir_statements() -> usize {
    5 // memory + memory_acc + public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            // AIR
            table.n_committed_columns()
            + table.n_down_columns_f() + table.n_down_columns_ef() * DIMENSION
            // Lookups into memory
            + table.lookups_f().iter().map(|lookup| 1 + lookup.values.len()).sum::<usize>()
            + table.lookups_ef().len() * (1 + DIMENSION)
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
}
