use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KOALABEAR_RC16_INTERNAL, KOALABEAR_RC24_INTERNAL};
use poseidon_circuit::{GKRPoseidonResult, PoseidonGKRLayers, default_cube_layers};
use sub_protocols::ColDims;

use crate::*;
use lean_vm::*;

pub(crate) const N_COMMITED_CUBES_P16: usize = KOALABEAR_RC16_INTERNAL.len() - 2;
pub(crate) const N_COMMITED_CUBES_P24: usize = KOALABEAR_RC24_INTERNAL.len() - 2;

pub(crate) fn get_base_dims(
    n_cycles: usize,
    log_public_memory: usize,
    private_memory_len: usize,
    n_poseidons_16: usize,
    n_poseidons_24: usize,
    n_rows_table_dot_products: usize,
    (p16_gkr_layers, p24_gkr_layers): (
        &PoseidonGKRLayers<16, N_COMMITED_CUBES_P16>,
        &PoseidonGKRLayers<24, N_COMMITED_CUBES_P24>,
    ),
) -> Vec<ColDims<F>> {
    let n_poseidons_16 = n_poseidons_16.max(MIN_N_ROWS_PER_TABLE);
    let n_poseidons_24 = n_poseidons_24.max(MIN_N_ROWS_PER_TABLE);
    let n_rows_table_dot_products = n_rows_table_dot_products.max(MIN_N_ROWS_PER_TABLE);

    let p16_default_cubes = default_cube_layers::<F, 16, N_COMMITED_CUBES_P16>(p16_gkr_layers);
    let p24_default_cubes = default_cube_layers::<F, 24, N_COMMITED_CUBES_P24>(p24_gkr_layers);

    [
        vec![
            ColDims::padded_with_public_data(Some(log_public_memory), private_memory_len, F::ZERO), //  memory
        ],
        Table::execution().committed_dims(n_cycles),
        Table::poseidon16().committed_dims(n_poseidons_16),
        p16_default_cubes
            .iter()
            .map(|&c| ColDims::padded(n_poseidons_16, c))
            .collect::<Vec<_>>(), // commited cubes for poseidon16
        Table::poseidon24().committed_dims(n_poseidons_24),
        p24_default_cubes
            .iter()
            .map(|&c| ColDims::padded(n_poseidons_24, c))
            .collect::<Vec<_>>(), // commited cubes for poseidon24
        Table::dot_product().committed_dims(n_rows_table_dot_products),
    ]
    .concat()
}

pub(crate) fn fold_bytecode(
    bytecode: &Bytecode,
    folding_challenges: &MultilinearPoint<EF>,
) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear_chunks(&encoded_bytecode, folding_challenges)
}

pub(crate) fn initial_and_final_pc_conditions(
    log_n_cycles: usize,
) -> (Evaluation<EF>, Evaluation<EF>) {
    let initial_pc_statement =
        Evaluation::new(EF::zero_vec(log_n_cycles), EF::from_usize(STARTING_PC));
    let final_pc_statement =
        Evaluation::new(vec![EF::ONE; log_n_cycles], EF::from_usize(ENDING_PC));
    (initial_pc_statement, final_pc_statement)
}

pub(crate) fn poseidon_lookup_statements(
    p16_gkr: &GKRPoseidonResult,
    p24_gkr: &GKRPoseidonResult,
) -> Vec<Vec<MultiEvaluation<EF>>> {
    vec![
        vec![MultiEvaluation::new(
            p16_gkr.input_statements.point.clone(),
            p16_gkr.input_statements.values[..VECTOR_LEN].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p16_gkr.input_statements.point.clone(),
            p16_gkr.input_statements.values[VECTOR_LEN..].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p16_gkr.output_statements.point.clone(),
            p16_gkr.output_statements.values[..VECTOR_LEN].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p16_gkr.output_statements.point.clone(),
            p16_gkr.output_statements.values[VECTOR_LEN..].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p24_gkr.input_statements.point.clone(),
            p24_gkr.input_statements.values[..VECTOR_LEN].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p24_gkr.input_statements.point.clone(),
            p24_gkr.input_statements.values[VECTOR_LEN..VECTOR_LEN * 2].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p24_gkr.input_statements.point.clone(),
            p24_gkr.input_statements.values[VECTOR_LEN * 2..].to_vec(),
        )],
        vec![MultiEvaluation::new(
            p24_gkr.output_statements.point.clone(),
            p24_gkr.output_statements.values[VECTOR_LEN * 2..].to_vec(),
        )],
    ]
}
