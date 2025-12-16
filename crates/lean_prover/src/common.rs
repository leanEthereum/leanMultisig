use std::collections::BTreeMap;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::KOALABEAR_RC16_INTERNAL;

use crate::*;
use lean_vm::*;

pub(crate) const N_COMMITED_CUBES_P16: usize = KOALABEAR_RC16_INTERNAL.len() - 2;

pub(crate) fn get_base_dims(log_memory: usize, table_heights: &BTreeMap<Table, VarCount>) -> Vec<VarCount> {
    let mut dims = vec![
        log_memory, //  memory
        log_memory, //  memory access counts (logup)
    ];
    for (table, log_n_rows) in table_heights {
        dims.extend(table.committed_dims(*log_n_rows));
    }
    dims
}

pub(crate) fn fold_bytecode(bytecode: &Bytecode, folding_challenges: &MultilinearPoint<EF>) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear_chunks(&encoded_bytecode, folding_challenges)
}

pub(crate) fn initial_and_final_pc_conditions(log_n_cycles: usize) -> (Evaluation<EF>, Evaluation<EF>) {
    let initial_pc_statement = Evaluation::new(EF::zero_vec(log_n_cycles), EF::from_usize(STARTING_PC));
    let final_pc_statement = Evaluation::new(vec![EF::ONE; log_n_cycles], EF::from_usize(ENDING_PC));
    (initial_pc_statement, final_pc_statement)
}

fn split_at(stmt: &MultiEvaluation<EF>, start: usize, end: usize) -> Vec<MultiEvaluation<EF>> {
    vec![MultiEvaluation::new(
        stmt.point.clone(),
        stmt.values[start..end].to_vec(),
    )]
}
