use lean_vm::{COL_INDEX_PC, CommittedStatements, ENDING_PC, STARTING_PC, sort_tables_by_height};
use lean_vm::{EF, F, Table, TableT, TableTrace};
use multilinear_toolkit::prelude::*;
use p3_util::log2_ceil_usize;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::{VarCount, transpose_slice_to_basis_coefficients};
use whir_p3::*;

#[derive(Debug)]
pub struct MultiCommitmentWitness {
    pub packed_n_vars: usize,
    pub inner_witness: Witness<EF>,
    pub packed_polynomial: MleOwned<EF>,
}

#[instrument(skip_all)]
pub fn packed_pcs_global_statements(
    packed_n_vars: usize,
    memory_n_vars: usize,
    memory_acc_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);

    let mut global_statements = memory_acc_statements;
    let mut offset = 2 << memory_n_vars;

    for (table, n_vars) in tables_heights_sorted {
        if table.is_execution_table() {
            // Important: ensure both initial and final PC conditions are correct
            global_statements.push(SparseStatement::unique_value(
                packed_n_vars,
                offset + (COL_INDEX_PC << n_vars),
                EF::from_usize(STARTING_PC),
            ));
            global_statements.push(SparseStatement::unique_value(
                packed_n_vars,
                offset + ((COL_INDEX_PC + 1) << n_vars) - 1,
                EF::from_usize(ENDING_PC),
            ));
        }
        for (point, col_statements) in &committed_statements[&table] {
            global_statements.push(SparseStatement::new(
                packed_n_vars,
                point.clone(),
                col_statements
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
        offset += table.n_commited_columns() << n_vars;
    }
    global_statements
}

#[instrument(skip_all)]
pub fn packed_pcs_commit(
    prover_state: &mut impl FSProver<EF>,
    whir_config_builder: &WhirConfigBuilder,
    memory: &[F],
    acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> MultiCommitmentWitness {
    assert_eq!(memory.len(), acc.len());
    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);

    let packed_n_vars = compute_total_n_vars(
        log2_strict_usize(memory.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut packed_polynomial = F::zero_vec(1 << packed_n_vars); // TODO avoid cloning all witness data
    packed_polynomial[..memory.len()].copy_from_slice(memory);
    let mut offset = memory.len();
    packed_polynomial[offset..offset + acc.len()].copy_from_slice(acc);
    offset += acc.len();
    for (table, log_n_rows) in &tables_heights_sorted {
        let n_rows = 1 << *log_n_rows;
        for col_index_f in 0..table.n_commited_columns_f() {
            let col = &traces[table].base[col_index_f];
            packed_polynomial[offset..offset + n_rows].copy_from_slice(&col[..n_rows]);
            offset += n_rows;
        }
        for col_index_ef in 0..table.n_commited_columns_ef() {
            let col = &traces[table].ext[col_index_ef];
            let transposed = transpose_slice_to_basis_coefficients(col);
            for basis_col in transposed {
                packed_polynomial[offset..offset + n_rows].copy_from_slice(&basis_col);
                offset += n_rows;
            }
        }
    }
    assert_eq!(log2_ceil_usize(offset), packed_n_vars);
    tracing::info!("packed PCS data: {} = 2^{:.2}", offset, (offset as f64).log2());

    let packed_polynomial = MleOwned::Base(packed_polynomial);

    let inner_witness = WhirConfig::new(whir_config_builder, packed_n_vars).commit(prover_state, &packed_polynomial);
    MultiCommitmentWitness {
        packed_n_vars,
        inner_witness,
        packed_polynomial,
    }
}

pub fn packed_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    log_memory: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    let packed_n_vars = compute_total_n_vars(log_memory, tables_heights);
    WhirConfig::new(whir_config_builder, packed_n_vars).parse_commitment(verifier_state)
}

fn compute_total_n_vars(log_memory: usize, tables_heights: &BTreeMap<Table, VarCount>) -> usize {
    let total_len = (2 << log_memory)
        + tables_heights
            .iter()
            .map(|(table, log_n_rows)| table.n_commited_columns() << log_n_rows)
            .sum::<usize>();
    log2_ceil_usize(total_len)
}
