use std::collections::BTreeMap;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KOALABEAR_RC16_INTERNAL, KOALABEAR_RC24_INTERNAL};
use poseidon_circuit::{PoseidonGKRLayers, default_cube_layers};
use sub_protocols::ColDims;

use crate::*;
use lean_vm::*;

pub(crate) const N_COMMITED_CUBES_P16: usize = KOALABEAR_RC16_INTERNAL.len() - 2;
pub(crate) const N_COMMITED_CUBES_P24: usize = KOALABEAR_RC24_INTERNAL.len() - 2;

pub(crate) fn get_base_dims(
    log_public_memory: usize,
    private_memory_len: usize,
    (p16_gkr_layers, p24_gkr_layers): (
        &PoseidonGKRLayers<16, N_COMMITED_CUBES_P16>,
        &PoseidonGKRLayers<24, N_COMMITED_CUBES_P24>,
    ),
    table_heights: &BTreeMap<Table, TableHeight>,
) -> Vec<ColDims<F>> {
    let p16_default_cubes = default_cube_layers::<F, 16, N_COMMITED_CUBES_P16>(p16_gkr_layers);
    let p24_default_cubes = default_cube_layers::<F, 24, N_COMMITED_CUBES_P24>(p24_gkr_layers);

    let mut dims = [
        vec![
            ColDims::padded_with_public_data(Some(log_public_memory), private_memory_len, F::ZERO), //  memory
            ColDims::padded((1 << log_public_memory) + private_memory_len, F::ZERO), //  memory access counts (logup)
        ],
        p16_default_cubes
            .iter()
            .map(|&c| ColDims::padded(table_heights[&Table::poseidon16_core()].n_rows_non_padded_maxed(), c))
            .collect::<Vec<_>>(), // commited cubes for poseidon16
        p24_default_cubes
            .iter()
            .map(|&c| ColDims::padded(table_heights[&Table::poseidon24_core()].n_rows_non_padded_maxed(), c))
            .collect::<Vec<_>>(),
    ]
    .concat();
    for (table, height) in table_heights {
        dims.extend(table.committed_dims(height.n_rows_non_padded_maxed()));
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
