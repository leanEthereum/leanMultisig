use lean_vm::sort_tables_by_height;
use lean_vm::{EF, F, Table, TableT, TableTrace};
use multilinear_toolkit::prelude::*;
use p3_util::log2_ceil_usize;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::{VarCount, to_big_endian_in_field, transpose_slice_to_basis_coefficients};
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
    tables_heights: &BTreeMap<Table, VarCount>,
    memory_statements: &[Evaluation<EF>],
    acc_statements: &[Evaluation<EF>],
    commited_statements: &BTreeMap<Table, Vec<Vec<Evaluation<EF>>>>,
) -> Vec<Evaluation<EF>> {
    let memory_n_vars = memory_statements[0].point.len();
    assert!(memory_statements.iter().all(|s| s.point.len() == memory_n_vars));
    assert!(acc_statements.iter().all(|s| s.point.len() == memory_n_vars));
    assert_eq!(tables_heights.len(), commited_statements.len());

    let tables_heights_sorted = sort_tables_by_height(tables_heights);

    let mut global_statements = Vec::new();
    let mut offset = 0;

    {
        // memory
        let selector = to_big_endian_in_field(offset >> memory_n_vars, packed_n_vars - memory_n_vars);
        for statement in memory_statements {
            let packed_point = MultilinearPoint([selector.clone(), statement.point.0.clone()].concat());
            global_statements.push(Evaluation::new(packed_point, statement.value));
        }
        offset += 1 << memory_n_vars;
    }

    {
        // accumulator
        let selector = to_big_endian_in_field(offset >> memory_n_vars, packed_n_vars - memory_n_vars);
        for statement in acc_statements {
            let packed_point = MultilinearPoint([selector.clone(), statement.point.0.clone()].concat());
            global_statements.push(Evaluation::new(packed_point, statement.value));
        }
        offset += 1 << memory_n_vars;
    }

    for (table, n_vars) in tables_heights_sorted {
        for col_statements_f in &commited_statements[&table] {
            let selector = to_big_endian_in_field(offset >> n_vars, packed_n_vars - n_vars);
            for statement in col_statements_f {
                let packed_point = MultilinearPoint([selector.clone(), statement.point.0.clone()].concat());
                global_statements.push(Evaluation::new(packed_point, statement.value));
            }
            offset += 1 << n_vars;
        }
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
