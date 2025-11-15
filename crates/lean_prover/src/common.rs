use multilinear_toolkit::prelude::*;
use p3_koala_bear::{KOALABEAR_RC16_INTERNAL, KOALABEAR_RC24_INTERNAL};
use p3_util::log2_ceil_usize;
use poseidon_circuit::{GKRPoseidonResult, PoseidonGKRLayers, default_cube_layers};
use sub_protocols::{ColDims, committed_dims_extension_from_base};
use vm_air::*;

use crate::*;
use lean_vm::*;

pub(crate) const N_COMMITED_CUBES_P16: usize = KOALABEAR_RC16_INTERNAL.len() - 2;
pub(crate) const N_COMMITED_CUBES_P24: usize = KOALABEAR_RC24_INTERNAL.len() - 2;

pub fn get_base_dims(
    n_cycles: usize,
    log_public_memory: usize,
    private_memory_len: usize,
    bytecode_ending_pc: usize,
    (n_poseidons_16, n_poseidons_24): (usize, usize),
    n_rows_table_dot_products: usize,
    (p16_gkr_layers, p24_gkr_layers): (
        &PoseidonGKRLayers<16, N_COMMITED_CUBES_P16>,
        &PoseidonGKRLayers<24, N_COMMITED_CUBES_P24>,
    ),
) -> Vec<ColDims<F>> {
    let n_poseidons_16 = n_poseidons_16.max(1 << LOG_MIN_POSEIDONS_16);
    let n_poseidons_24 = n_poseidons_24.max(1 << LOG_MIN_POSEIDONS_24);
    let n_rows_table_dot_products = n_rows_table_dot_products.max(1 << LOG_MIN_DOT_PRODUCT_ROWS);

    let p16_default_cubes = default_cube_layers::<F, 16, N_COMMITED_CUBES_P16>(p16_gkr_layers);
    let p24_default_cubes = default_cube_layers::<F, 24, N_COMMITED_CUBES_P24>(p24_gkr_layers);

    [
        vec![
            ColDims::padded_with_public_data(Some(log_public_memory), private_memory_len, F::ZERO), //  memory
            ColDims::padded(n_cycles, F::from_usize(bytecode_ending_pc)), // pc
            ColDims::padded(n_cycles, F::ZERO),                           // fp
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_a
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_b
            ColDims::padded(n_cycles, F::ZERO),                           // mem_addr_c
            ColDims::padded(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index a
            ColDims::padded(n_poseidons_16, F::from_usize(ZERO_VEC_PTR)), // poseidon16 index b
            ColDims::padded(n_poseidons_16, F::from_usize(POSEIDON_16_NULL_HASH_PTR)), // poseidon16 index res
            ColDims::padded(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index a
            ColDims::padded(n_poseidons_24, F::from_usize(ZERO_VEC_PTR)), // poseidon24 index b
            ColDims::padded(n_poseidons_24, F::from_usize(POSEIDON_24_NULL_HASH_PTR)), // poseidon24 index res
        ],
        p16_default_cubes
            .iter()
            .map(|&c| ColDims::padded(n_poseidons_16, c))
            .collect::<Vec<_>>(), // commited cubes for poseidon16
        p24_default_cubes
            .iter()
            .map(|&c| ColDims::padded(n_poseidons_24, c))
            .collect::<Vec<_>>(), // commited cubes for poseidon24
        vec![
            ColDims::padded(n_rows_table_dot_products, F::ONE), // dot product: (start) flag
            ColDims::padded(n_rows_table_dot_products, F::ONE), // dot product: length
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index a
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index b
            ColDims::padded(n_rows_table_dot_products, F::ZERO), // dot product: index res
        ],
        committed_dims_extension_from_base(n_rows_table_dot_products, EF::ZERO), // dot product: computation
    ]
    .concat()
}

pub fn normal_lookup_into_memory_initial_statements(
    exec_air_point: &MultilinearPoint<EF>,
    exec_evals: &[EF],
    dot_product_air_point: &MultilinearPoint<EF>,
    dot_product_evals: &[EF],
) -> Vec<Vec<Evaluation<EF>>> {
    [
        [
            COL_INDEX_MEM_VALUE_A,
            COL_INDEX_MEM_VALUE_B,
            COL_INDEX_MEM_VALUE_C,
        ]
        .into_iter()
        .map(|index| vec![Evaluation::new(exec_air_point.clone(), exec_evals[index])])
        .collect::<Vec<_>>(),
        [
            DOT_PRODUCT_AIR_COL_VALUE_A,
            DOT_PRODUCT_AIR_COL_VALUE_B,
            DOT_PRODUCT_AIR_COL_VALUE_RES,
        ]
        .into_iter()
        .map(|index| {
            vec![Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_evals[index],
            )]
        })
        .collect::<Vec<_>>(),
    ]
    .concat()
}

pub fn fold_bytecode(bytecode: &Bytecode, folding_challenges: &MultilinearPoint<EF>) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear_chunks(&encoded_bytecode, folding_challenges)
}

pub fn initial_and_final_pc_conditions(
    bytecode: &Bytecode,
    log_n_cycles: usize,
) -> (Evaluation<EF>, Evaluation<EF>) {
    let initial_pc_statement = Evaluation::new(EF::zero_vec(log_n_cycles), EF::ZERO);
    let final_pc_statement = Evaluation::new(
        vec![EF::ONE; log_n_cycles],
        EF::from_usize(bytecode.ending_pc),
    );
    (initial_pc_statement, final_pc_statement)
}

pub fn add_memory_statements_for_dot_product_precompile(
    entry: &RowMultilinearEval,
    log_memory: usize,
    log_public_memory: usize,
    challenger: &mut impl ChallengeSampler<EF>,
    memory_statements: &mut Vec<Evaluation<EF>>,
) -> Result<(), ProofError> {
    // point lookup into memory
    let log_point_len = log2_ceil_usize(entry.n_vars() * DIMENSION);
    let point_random_challenge = challenger.sample_vec(log_point_len);
    let point_random_value = {
        let mut point_mle = flatten_scalars_to_base::<PF<EF>, EF>(&entry.point);
        point_mle.resize(point_mle.len().next_power_of_two(), F::ZERO);
        point_mle.evaluate(&MultilinearPoint(point_random_challenge.clone()))
    };
    memory_statements.push(Evaluation::new(
        [
            to_big_endian_in_field(entry.addr_point, log_memory - log_point_len),
            point_random_challenge.clone(),
        ]
        .concat(),
        point_random_value,
    ));

    // result lookup into memory
    let random_challenge = challenger.sample_vec(LOG_VECTOR_LEN);
    let res_random_value = {
        let mut res_mle = entry.res.as_basis_coefficients_slice().to_vec();
        res_mle.resize(VECTOR_LEN, F::ZERO);
        res_mle.evaluate(&MultilinearPoint(random_challenge.clone()))
    };
    memory_statements.push(Evaluation::new(
        [
            to_big_endian_in_field(entry.addr_res, log_memory - LOG_VECTOR_LEN),
            random_challenge.clone(),
        ]
        .concat(),
        res_random_value,
    ));

    {
        if entry.n_vars() > log_memory {
            return Err(ProofError::InvalidProof);
        }
        if entry.addr_coeffs >= 1 << (log_memory - entry.n_vars()) {
            return Err(ProofError::InvalidProof);
        }
        if entry.n_vars() >= log_public_memory {
            todo!("vm multilinear eval across multiple memory chunks")
        }
        let addr_bits = to_big_endian_in_field(entry.addr_coeffs, log_memory - entry.n_vars());
        let statement = Evaluation::new([addr_bits, entry.point.clone()].concat(), entry.res);
        memory_statements.push(statement);
    }

    Ok(())
}

pub fn default_poseidon_indexes() -> Vec<usize> {
    [
        vec![
            ZERO_VEC_PTR,
            ZERO_VEC_PTR,
            POSEIDON_16_NULL_HASH_PTR,
            if POSEIDON_16_DEFAULT_COMPRESSION {
                ZERO_VEC_PTR
            } else {
                POSEIDON_16_NULL_HASH_PTR + 1
            },
        ],
        vec![
            ZERO_VEC_PTR,
            ZERO_VEC_PTR,
            ZERO_VEC_PTR,
            POSEIDON_24_NULL_HASH_PTR,
        ],
    ]
    .concat()
}

pub fn poseidon_lookup_statements(
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
