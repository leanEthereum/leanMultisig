use crate::common::*;
use crate::*;
use ::air::table::AirTable;
use lean_vm::*;
use lookup::verify_gkr_product;
use lookup::verify_logup_star;
use p3_air::BaseAir;
use p3_field::BasedVectorSpace;
use p3_field::PrimeCharacteristicRing;
use p3_field::dot_product;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use packed_pcs::*;
use sumcheck::SumcheckComputation;
use utils::dot_product_with_base;
use utils::{PF, build_challenger, padd_with_zero_to_next_power_of_two};
use utils::{ToUsize, build_poseidon_16_air, build_poseidon_24_air};
use vm_air::*;
use whir_p3::fiat_shamir::{errors::ProofError, verifier::VerifierState};
use whir_p3::poly::evals::EvaluationsList;
use whir_p3::poly::evals::eval_eq;
use whir_p3::poly::multilinear::Evaluation;
use whir_p3::poly::multilinear::MultilinearPoint;
use whir_p3::utils::flatten_scalars_to_base;
use whir_p3::whir::config::WhirConfig;
use whir_p3::whir::config::second_batched_whir_config_builder;

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof_data: Vec<PF<EF>>,
    whir_config_builder: MyWhirConfigBuilder,
) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::new(proof_data, build_challenger());

    let exec_table = AirTable::<EF, _, _>::new(VMAir, VMAir);
    let p16_air = build_poseidon_16_air();
    let p24_air = build_poseidon_24_air();
    let p16_air_packed = build_poseidon_16_air_packed();
    let p24_air_packed = build_poseidon_24_air_packed();
    let p16_table = AirTable::<EF, _, _>::new(p16_air.clone(), p16_air_packed);
    let p24_table = AirTable::<EF, _, _>::new(p24_air.clone(), p24_air_packed);
    let dot_product_table = AirTable::<EF, _, _>::new(DotProductAir, DotProductAir);

    let [
        log_n_cycles,
        n_poseidons_16,
        n_poseidons_24,
        n_dot_products,
        n_rows_table_dot_products,
        private_memory_len,
        n_vm_multilinear_evals,
    ] = verifier_state
        .next_base_scalars_const::<7>()?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    if log_n_cycles > 32
        || n_poseidons_16 > 1 << 32
        || n_poseidons_24 > 1 << 32
        || n_dot_products > 1 << 32
        || n_rows_table_dot_products > 1 << 32
        || private_memory_len > 1 << 32
        || n_vm_multilinear_evals > 1 << 10
    {
        // To avoid "DOS" attack
        return Err(ProofError::InvalidProof);
    }
    let n_cycles = 1 << log_n_cycles;

    let public_memory = build_public_memory(public_input);

    let log_public_memory = log2_strict_usize(public_memory.len());
    let log_memory = log2_ceil_usize(public_memory.len() + private_memory_len);
    let log_n_p16 = log2_ceil_usize(n_poseidons_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let table_dot_products_log_n_rows = log2_ceil_usize(n_rows_table_dot_products);
    let dot_product_padding_len =
        n_rows_table_dot_products.next_power_of_two() - n_rows_table_dot_products;

    struct RowMultilinearEval {
        addr_coeffs: F,
        addr_point: F,
        addr_res: F,
        n_vars: F,
        point: Vec<EF>,
        res: EF,
    }

    let mut vm_multilinear_evals = Vec::new();
    for _ in 0..n_vm_multilinear_evals {
        let [addr_coeffs, addr_point, addr_res, n_vars] =
            verifier_state.next_base_scalars_const::<4>()?;
        let point = verifier_state.next_extension_scalars_vec(n_vars.to_usize())?;
        let res = verifier_state.next_extension_scalar()?;
        vm_multilinear_evals.push(RowMultilinearEval {
            addr_coeffs,
            addr_point,
            addr_res,
            n_vars,
            point,
            res,
        });
    }

    let mut memory_statements = vec![];
    for row_multilinear_eval in &vm_multilinear_evals {
        let addr_point = row_multilinear_eval.addr_point.to_usize();
        let addr_coeffs = row_multilinear_eval.addr_coeffs.to_usize();
        let addr_res = row_multilinear_eval.addr_res.to_usize();
        let n_vars = row_multilinear_eval.n_vars.to_usize();

        // point lookup into memory
        let log_point_len = log2_ceil_usize(row_multilinear_eval.point.len() * DIMENSION);
        let point_random_challenge = verifier_state.sample_vec(log_point_len);
        let point_random_value = {
            let mut point_mle = flatten_scalars_to_base::<PF<EF>, EF>(&row_multilinear_eval.point);
            point_mle.resize(point_mle.len().next_power_of_two(), F::ZERO);
            point_mle.evaluate(&MultilinearPoint(point_random_challenge.clone()))
        };
        memory_statements.push(Evaluation::new(
            [
                to_big_endian_in_field(addr_point, log_memory - log_point_len),
                point_random_challenge.clone(),
            ]
            .concat(),
            point_random_value,
        ));

        // result lookup into memory
        let random_challenge = verifier_state.sample_vec(LOG_VECTOR_LEN);
        let res_random_value = {
            let mut res_mle = row_multilinear_eval
                .res
                .as_basis_coefficients_slice()
                .to_vec();
            res_mle.resize(VECTOR_LEN, F::ZERO);
            res_mle.evaluate(&MultilinearPoint(random_challenge.clone()))
        };
        memory_statements.push(Evaluation::new(
            [
                to_big_endian_in_field(addr_res, log_memory - LOG_VECTOR_LEN),
                random_challenge.clone(),
            ]
            .concat(),
            res_random_value,
        ));

        {
            if n_vars > log_memory {
                return Err(ProofError::InvalidProof);
            }
            if addr_coeffs >= 1 << (log_memory - n_vars) {
                return Err(ProofError::InvalidProof);
            }
            if n_vars >= log_public_memory {
                todo!("vm multilinear eval accross multiple memory chunks")
            }
            let addr_bits = to_big_endian_in_field(addr_coeffs, log_memory - n_vars);
            let statement = Evaluation::new(
                [addr_bits, row_multilinear_eval.point.clone()].concat(),
                row_multilinear_eval.res,
            );
            memory_statements.push(statement);
        }
    }

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory_len,
        bytecode.ending_pc,
        (n_poseidons_16, n_poseidons_24),
        (p16_air.width(), p24_air.width()),
        n_rows_table_dot_products,
    );

    let parsed_commitment_base = packed_pcs_parse_commitment(
        &whir_config_builder,
        &mut verifier_state,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )?;

    let grand_product_challenge_global = verifier_state.sample();
    let grand_product_challenge_p16 = verifier_state.sample().powers().collect_n(5);
    let grand_product_challenge_p24 = verifier_state.sample().powers().collect_n(5);
    let grand_product_challenge_dot_product = verifier_state.sample().powers().collect_n(6);
    let grand_product_challenge_vm_multilinear_eval = verifier_state.sample().powers().collect_n(6);
    let (grand_product_exec_res, grand_product_exec_statement) =
        verify_gkr_product(&mut verifier_state, log_n_cycles)?;
    let (grand_product_p16_res, grand_product_p16_statement) =
        verify_gkr_product(&mut verifier_state, log_n_p16)?;
    let (grand_product_p24_res, grand_product_p24_statement) =
        verify_gkr_product(&mut verifier_state, log_n_p24)?;
    let (grand_product_dot_product_res, grand_product_dot_product_statement) =
        verify_gkr_product(&mut verifier_state, table_dot_products_log_n_rows)?;
    let vm_multilinear_eval_grand_product_res = vm_multilinear_evals
        .iter()
        .map(|vm_multilinear_eval| {
            grand_product_challenge_global
                + grand_product_challenge_vm_multilinear_eval[1]
                + grand_product_challenge_vm_multilinear_eval[2] * vm_multilinear_eval.addr_coeffs
                + grand_product_challenge_vm_multilinear_eval[3] * vm_multilinear_eval.addr_point
                + grand_product_challenge_vm_multilinear_eval[4] * vm_multilinear_eval.addr_res
                + grand_product_challenge_vm_multilinear_eval[5] * vm_multilinear_eval.n_vars
        })
        .product::<EF>();

    let corrected_prod_exec = grand_product_exec_res
        / grand_product_challenge_global.exp_u64(
            (n_cycles
                - n_poseidons_16
                - n_poseidons_24
                - n_dot_products
                - vm_multilinear_evals.len()) as u64,
        );
    let corrected_prod_p16 = grand_product_p16_res
        / (grand_product_challenge_global
            + grand_product_challenge_p16[1]
            + grand_product_challenge_p16[4] * F::from_usize(POSEIDON_16_NULL_HASH_PTR))
        .exp_u64((n_poseidons_16.next_power_of_two() - n_poseidons_16) as u64);

    let corrected_prod_p24 = grand_product_p24_res
        / (grand_product_challenge_global
            + grand_product_challenge_p24[1]
            + grand_product_challenge_p24[4] * F::from_usize(POSEIDON_24_NULL_HASH_PTR))
        .exp_u64((n_poseidons_24.next_power_of_two() - n_poseidons_24) as u64);

    let corrected_dot_product = grand_product_dot_product_res
        / ((grand_product_challenge_global
            + grand_product_challenge_dot_product[1]
            + grand_product_challenge_dot_product[5])
            .exp_u64(dot_product_padding_len as u64)
            * (grand_product_challenge_global + grand_product_challenge_dot_product[1]).exp_u64(
                ((1 << table_dot_products_log_n_rows) - dot_product_padding_len - n_dot_products)
                    as u64,
            ));

    if corrected_prod_exec
        != corrected_prod_p16
            * corrected_prod_p24
            * corrected_dot_product
            * vm_multilinear_eval_grand_product_res
    {
        return Err(ProofError::InvalidProof);
    }

    let [
        p16_grand_product_evals_on_indexes_a,
        p16_grand_product_evals_on_indexes_b,
        p16_grand_product_evals_on_indexes_res,
    ] = verifier_state.next_extension_scalars_const()?;
    if grand_product_challenge_global
        + grand_product_challenge_p16[1]
        + grand_product_challenge_p16[2] * p16_grand_product_evals_on_indexes_a
        + grand_product_challenge_p16[3] * p16_grand_product_evals_on_indexes_b
        + grand_product_challenge_p16[4] * p16_grand_product_evals_on_indexes_res
        != grand_product_p16_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    let mut p16_indexes_a_statements = vec![Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_a,
    )];
    let mut p16_indexes_b_statements = vec![Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_b,
    )];
    let mut p16_indexes_res_statements = vec![Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_res,
    )];

    let [
        p24_grand_product_evals_on_indexes_a,
        p24_grand_product_evals_on_indexes_b,
        p24_grand_product_evals_on_indexes_res,
    ] = verifier_state.next_extension_scalars_const()?;
    if grand_product_challenge_global
        + grand_product_challenge_p24[1]
        + grand_product_challenge_p24[2] * p24_grand_product_evals_on_indexes_a
        + grand_product_challenge_p24[3] * p24_grand_product_evals_on_indexes_b
        + grand_product_challenge_p24[4] * p24_grand_product_evals_on_indexes_res
        != grand_product_p24_statement.value
    {
        return Err(ProofError::InvalidProof);
    }

    let mut p24_indexes_a_statements = vec![Evaluation::new(
        grand_product_p24_statement.point.clone(),
        p24_grand_product_evals_on_indexes_a,
    )];
    let mut p24_indexes_b_statements = vec![Evaluation::new(
        grand_product_p24_statement.point.clone(),
        p24_grand_product_evals_on_indexes_b,
    )];
    let mut p24_indexes_res_statements = vec![Evaluation::new(
        grand_product_p24_statement.point.clone(),
        p24_grand_product_evals_on_indexes_res,
    )];

    // Grand product statements
    let (grand_product_final_dot_product_eval, grand_product_dot_product_sumcheck_claim) =
        sumcheck::verify(&mut verifier_state, table_dot_products_log_n_rows, 3)?;
    if grand_product_final_dot_product_eval != grand_product_dot_product_statement.value {
        return Err(ProofError::InvalidProof);
    }
    let grand_product_dot_product_sumcheck_inner_evals =
        verifier_state.next_extension_scalars_vec(5)?;

    if grand_product_dot_product_sumcheck_claim.value
        != grand_product_dot_product_sumcheck_claim
            .point
            .eq_poly_outside(&grand_product_dot_product_statement.point)
            * {
                DotProductFootprint {
                    grand_product_challenge_global,
                    grand_product_challenge_dot_product: grand_product_challenge_dot_product
                        .clone()
                        .try_into()
                        .unwrap(),
                }
                .eval(&grand_product_dot_product_sumcheck_inner_evals, &[])
            }
    {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_dot_product_flag_statement = Evaluation::new(
        grand_product_dot_product_sumcheck_claim.point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[0],
    );
    let grand_product_dot_product_len_statement = Evaluation::new(
        grand_product_dot_product_sumcheck_claim.point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[1],
    );
    let grand_product_dot_product_table_indexes_statement_index_a = Evaluation::new(
        grand_product_dot_product_sumcheck_claim.point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[2],
    );
    let grand_product_dot_product_table_indexes_statement_index_b = Evaluation::new(
        grand_product_dot_product_sumcheck_claim.point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[3],
    );
    let grand_product_dot_product_table_indexes_statement_index_res = Evaluation::new(
        grand_product_dot_product_sumcheck_claim.point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[4],
    );

    let (grand_product_final_exec_eval, grand_product_exec_sumcheck_claim) =
        sumcheck::verify(&mut verifier_state, log_n_cycles, 4)?;
    if grand_product_final_exec_eval != grand_product_exec_statement.value {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_exec_sumcheck_inner_evals =
        verifier_state.next_extension_scalars_vec(N_TOTAL_COLUMNS)?;

    let grand_product_exec_evals_on_each_column =
        &grand_product_exec_sumcheck_inner_evals[..N_INSTRUCTION_COLUMNS];

    if grand_product_exec_sumcheck_claim.value
        != grand_product_exec_sumcheck_claim
            .point
            .eq_poly_outside(&grand_product_exec_statement.point)
            * {
                PrecompileFootprint {
                    grand_product_challenge_global,
                    grand_product_challenge_p16: grand_product_challenge_p16.try_into().unwrap(),
                    grand_product_challenge_p24: grand_product_challenge_p24.try_into().unwrap(),
                    grand_product_challenge_dot_product: grand_product_challenge_dot_product
                        .try_into()
                        .unwrap(),
                    grand_product_challenge_vm_multilinear_eval:
                        grand_product_challenge_vm_multilinear_eval
                            .try_into()
                            .unwrap(),
                }
                .eval(&grand_product_exec_sumcheck_inner_evals, &[])
            }
    {
        return Err(ProofError::InvalidProof);
    }

    let grand_product_fp_statement = Evaluation::new(
        grand_product_exec_sumcheck_claim.point.clone(),
        grand_product_exec_sumcheck_inner_evals[COL_INDEX_FP],
    );

    let exec_evals_to_verify = exec_table.verify(
        &mut verifier_state,
        UNIVARIATE_SKIPS,
        log_n_cycles,
        &exec_column_groups(),
    )?;

    let dot_product_evals_to_verify = dot_product_table.verify(
        &mut verifier_state,
        1,
        table_dot_products_log_n_rows,
        &DOT_PRODUCT_AIR_COLUMN_GROUPS,
    )?;

    let p16_evals_to_verify = p16_table.verify(
        &mut verifier_state,
        UNIVARIATE_SKIPS,
        log_n_p16,
        &poseidon_16_column_groups(&p16_air),
    )?;
    let p24_evals_to_verify = p24_table.verify(
        &mut verifier_state,
        UNIVARIATE_SKIPS,
        log_n_p24,
        &poseidon_24_column_groups(&p24_air),
    )?;

    let poseidon_logup_star_alpha = verifier_state.sample();
    let memory_folding_challenges = MultilinearPoint(verifier_state.sample_vec(LOG_VECTOR_LEN));

    let non_used_precompiles_evals = verifier_state
        .next_extension_scalars_vec(N_INSTRUCTION_COLUMNS - N_INSTRUCTION_COLUMNS_IN_AIR)?;
    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    for i in 1..N_INSTRUCTION_COLUMNS_IN_AIR {
        assert_eq!(
            &exec_evals_to_verify[0].point,
            &exec_evals_to_verify[i].point
        );
    }
    let bytecode_lookup_point_1 = exec_evals_to_verify[0].point.clone();
    let bytecode_lookup_claim_1 = Evaluation::new(
        bytecode_lookup_point_1,
        padd_with_zero_to_next_power_of_two(
            &[
                (0..N_INSTRUCTION_COLUMNS_IN_AIR)
                    .map(|i| exec_evals_to_verify[i].value)
                    .collect::<Vec<_>>(),
                non_used_precompiles_evals,
            ]
            .concat(),
        )
        .evaluate(&bytecode_compression_challenges),
    );

    let bytecode_lookup_claim_2 = Evaluation::new(
        grand_product_exec_sumcheck_claim.point.clone(),
        padd_with_zero_to_next_power_of_two(grand_product_exec_evals_on_each_column)
            .evaluate(&bytecode_compression_challenges),
    );
    let alpha_bytecode_lookup = verifier_state.sample();

    let dot_product_evals_spread = verifier_state.next_extension_scalars_vec(DIMENSION)?;

    if dot_product_with_base(&dot_product_evals_spread) != dot_product_evals_to_verify[5].value {
        return Err(ProofError::InvalidProof);
    }
    let dot_product_values_batching_scalars = MultilinearPoint(verifier_state.sample_vec(3));
    let dot_product_values_batched_point = MultilinearPoint(
        [
            dot_product_values_batching_scalars.0.clone(),
            dot_product_evals_to_verify[5].point.0.clone(),
        ]
        .concat(),
    );
    let dot_product_values_batched_eval =
        padd_with_zero_to_next_power_of_two(&dot_product_evals_spread)
            .evaluate(&dot_product_values_batching_scalars);

    let unused_1 = verifier_state.next_extension_scalar()?;
    let grand_product_mem_values_mixing_challenges = MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_1 = Evaluation::new(
        [
            grand_product_mem_values_mixing_challenges.0.clone(),
            grand_product_exec_sumcheck_claim.point.0,
        ]
        .concat(),
        [
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_A],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_B],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_C],
            unused_1,
        ]
        .evaluate(&grand_product_mem_values_mixing_challenges),
    );

    let unused_2 = verifier_state.next_extension_scalar()?;
    let exec_air_mem_values_mixing_challenges = MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_2 = Evaluation::new(
        [
            exec_air_mem_values_mixing_challenges.0.clone(),
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_A.index_in_air()]
                .point
                .0
                .clone(),
        ]
        .concat(),
        [
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_A.index_in_air()].value,
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_B.index_in_air()].value,
            exec_evals_to_verify[COL_INDEX_MEM_VALUE_C.index_in_air()].value,
            unused_2,
        ]
        .evaluate(&exec_air_mem_values_mixing_challenges),
    );

    let [unused_3a, unused_3b, unused_3c] = verifier_state.next_extension_scalars_const()?;

    let dot_product_air_mem_values_mixing_challenges =
        MultilinearPoint(verifier_state.sample_vec(2));
    let base_memory_lookup_statement_3 = Evaluation::new(
        [
            dot_product_air_mem_values_mixing_challenges.0.clone(),
            EF::zero_vec(log_n_cycles - dot_product_values_batched_point.len()),
            dot_product_values_batched_point.0.clone(),
        ]
        .concat(),
        [
            unused_3a,
            unused_3b,
            unused_3c,
            dot_product_values_batched_eval,
        ]
        .evaluate(&dot_product_air_mem_values_mixing_challenges),
    );

    let memory_poly_eq_point_alpha = verifier_state.sample();

    let extension_dims = vec![
        ColDims::padded(public_memory.len() + private_memory_len, EF::ZERO), // memory
        ColDims::padded(
            (public_memory.len() + private_memory_len).div_ceil(VECTOR_LEN),
            EF::ZERO,
        ), // memory (folded)
        ColDims::padded(bytecode.instructions.len(), EF::ZERO),
    ];

    let parsed_commitment_extension = packed_pcs_parse_commitment(
        &second_batched_whir_config_builder::<EF, EF, _, _, _>(
            whir_config_builder.clone(),
            parsed_commitment_base.num_variables,
            num_packed_vars_for_dims::<EF>(&extension_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK),
        ),
        &mut verifier_state,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )
    .unwrap();

    let base_memory_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log_memory,
        log_n_cycles + 2,
        &[
            base_memory_lookup_statement_1,
            base_memory_lookup_statement_2,
            base_memory_lookup_statement_3,
        ],
        memory_poly_eq_point_alpha,
    )
    .unwrap();

    let p16_lookup_point = p16_evals_to_verify[0].point.0.clone();
    let p24_lookup_point = p24_evals_to_verify[0].point.0.clone();

    let max_n_poseidons = n_poseidons_16.max(n_poseidons_24).next_power_of_two();

    #[rustfmt::skip]
        let p16_folded_eval_addr_a = p16_evals_to_verify[..8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p16_folded_eval_addr_b = p16_evals_to_verify[8..16].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p16_folded_eval_addr_res_a = p16_evals_to_verify[p16_air.width() - 16..p16_air.width() - 8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p16_folded_eval_addr_res_b = p16_evals_to_verify[p16_air.width() - 8..].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);

    #[rustfmt::skip]
        let p24_folded_eval_addr_a = p24_evals_to_verify[..8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p24_folded_eval_addr_b = p24_evals_to_verify[8..16].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p24_folded_eval_addr_c = p24_evals_to_verify[16..24].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
    #[rustfmt::skip]
        let p24_folded_eval_addr_res = p24_evals_to_verify[p24_air.width() - 8..].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);

    let padding_p16 = EF::zero_vec(log2_ceil_usize(max_n_poseidons) - log_n_p16);
    let padding_p24 = EF::zero_vec(log2_ceil_usize(max_n_poseidons) - log_n_p24);

    let poseidon_lookup_statements = vec![
        Evaluation::new(
            [
                vec![EF::ZERO; 3],
                padding_p16.clone(),
                p16_lookup_point.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_a,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ZERO, EF::ONE],
                padding_p16.clone(),
                p16_lookup_point.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_b,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ONE, EF::ZERO],
                padding_p16.clone(),
                p16_lookup_point.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_res_a,
        ),
        Evaluation::new(
            [
                vec![EF::ZERO, EF::ONE, EF::ONE],
                padding_p16.clone(),
                p16_lookup_point.clone(),
            ]
            .concat(),
            p16_folded_eval_addr_res_b,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ZERO, EF::ZERO],
                padding_p24.clone(),
                p24_lookup_point.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_a,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ZERO, EF::ONE],
                padding_p24.clone(),
                p24_lookup_point.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_b,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ONE, EF::ZERO],
                padding_p24.clone(),
                p24_lookup_point.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_c,
        ),
        Evaluation::new(
            [
                vec![EF::ONE, EF::ONE, EF::ONE],
                padding_p24.clone(),
                p24_lookup_point.clone(),
            ]
            .concat(),
            p24_folded_eval_addr_res,
        ),
    ];

    let poseidon_lookup_log_length = 3 + log_n_p16.max(log_n_p24);
    let poseidon_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log_memory - 3, // "-3" because it's folded memory
        poseidon_lookup_log_length,
        &poseidon_lookup_statements,
        poseidon_logup_star_alpha,
    )
    .unwrap();

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        log_n_cycles,
        &[bytecode_lookup_claim_1, bytecode_lookup_claim_2],
        alpha_bytecode_lookup,
    )
    .unwrap();
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    let poseidon_lookup_memory_point = MultilinearPoint(
        [
            poseidon_logup_star_statements.on_table.point.0.clone(),
            memory_folding_challenges.0,
        ]
        .concat(),
    );

    memory_statements.push(base_memory_logup_star_statements.on_table.clone());
    memory_statements.push(Evaluation::new(
        poseidon_lookup_memory_point.clone(),
        poseidon_logup_star_statements.on_table.value,
    ));

    {
        // index opening for poseidon lookup

        let correcting_factor = poseidon_logup_star_statements.on_indexes.point
            [3..3 + log_n_p16.abs_diff(log_n_p24)]
            .iter()
            .map(|&x| EF::ONE - x)
            .product::<EF>();
        let (correcting_factor_p16, correcting_factor_p24) = if n_poseidons_16 > n_poseidons_24 {
            (EF::ONE, correcting_factor)
        } else {
            (correcting_factor, EF::ONE)
        };
        let mut idx_point_right_p16 =
            MultilinearPoint(poseidon_logup_star_statements.on_indexes.point[3..].to_vec());
        let mut idx_point_right_p24 = MultilinearPoint(
            poseidon_logup_star_statements.on_indexes.point[3 + log_n_p16.abs_diff(log_n_p24)..]
                .to_vec(),
        );
        if n_poseidons_16 < n_poseidons_24 {
            std::mem::swap(&mut idx_point_right_p16, &mut idx_point_right_p24);
        }

        let mut inner_values = verifier_state.next_extension_scalars_vec(6)?;
        p16_indexes_a_statements.push(Evaluation::new(
            idx_point_right_p16.clone(),
            inner_values[0],
        ));
        p16_indexes_b_statements.push(Evaluation::new(
            idx_point_right_p16.clone(),
            inner_values[1],
        ));
        p16_indexes_res_statements.push(Evaluation::new(
            idx_point_right_p16.clone(),
            inner_values[2],
        ));
        p24_indexes_a_statements.push(Evaluation::new(
            idx_point_right_p24.clone(),
            inner_values[3],
        ));
        p24_indexes_b_statements.push(Evaluation::new(
            idx_point_right_p24.clone(),
            inner_values[4],
        ));
        p24_indexes_res_statements.push(Evaluation::new(
            idx_point_right_p24.clone(),
            inner_values[5],
        ));

        inner_values.insert(3, inner_values[2] + EF::ONE);
        inner_values.insert(5, inner_values[4] + EF::ONE);

        for v in &mut inner_values[..4] {
            *v *= correcting_factor_p16;
        }
        for v in &mut inner_values[4..] {
            *v *= correcting_factor_p24;
        }

        assert_eq!(
            inner_values.evaluate(&MultilinearPoint(
                poseidon_logup_star_statements.on_indexes.point[..3].to_vec()
            )),
            poseidon_logup_star_statements.on_indexes.value
        );
    }

    let (initial_pc_statement, final_pc_statement) =
        intitial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_computation_column_evals =
        verifier_state.next_extension_scalars_const::<DIMENSION>()?;
    if dot_product_with_base(&dot_product_computation_column_evals)
        != dot_product_evals_to_verify[6].value
    {
        return Err(ProofError::InvalidProof);
    }
    let dot_product_computation_column_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation::new(
                dot_product_evals_to_verify[6].point.clone(),
                dot_product_computation_column_evals[i],
            )]
        })
        .collect::<Vec<_>>();

    let mem_lookup_eval_indexes_partial_point =
        MultilinearPoint(base_memory_logup_star_statements.on_indexes.point[2..].to_vec());
    let [
        mem_lookup_eval_indexes_a,
        mem_lookup_eval_indexes_b,
        mem_lookup_eval_indexes_c,
        mem_lookup_eval_spread_indexes_dot_product,
    ] = verifier_state.next_extension_scalars_const()?;

    let index_diff = log_n_cycles - (table_dot_products_log_n_rows + 5);

    assert_eq!(
        [
            mem_lookup_eval_indexes_a,
            mem_lookup_eval_indexes_b,
            mem_lookup_eval_indexes_c,
            mem_lookup_eval_spread_indexes_dot_product
                * mem_lookup_eval_indexes_partial_point[..index_diff]
                    .iter()
                    .map(|x| EF::ONE - *x)
                    .product::<EF>(),
        ]
        .evaluate(&MultilinearPoint(
            base_memory_logup_star_statements.on_indexes.point[..2].to_vec(),
        )),
        base_memory_logup_star_statements.on_indexes.value
    );

    let dot_product_logup_star_indexes_inner_point =
        MultilinearPoint(mem_lookup_eval_indexes_partial_point.0[5 + index_diff..].to_vec());

    let [
        dot_product_logup_star_indexes_inner_value_a,
        dot_product_logup_star_indexes_inner_value_b,
        dot_product_logup_star_indexes_inner_value_res,
    ] = verifier_state.next_extension_scalars_const()?;

    let dot_product_logup_star_indexes_statement_a = Evaluation::new(
        dot_product_logup_star_indexes_inner_point.clone(),
        dot_product_logup_star_indexes_inner_value_a,
    );
    let dot_product_logup_star_indexes_statement_b = Evaluation::new(
        dot_product_logup_star_indexes_inner_point.clone(),
        dot_product_logup_star_indexes_inner_value_b,
    );
    let dot_product_logup_star_indexes_statement_res = Evaluation::new(
        dot_product_logup_star_indexes_inner_point.clone(),
        dot_product_logup_star_indexes_inner_value_res,
    );

    {
        let dot_product_logup_star_indexes_inner_value: EF = dot_product(
            eval_eq(&mem_lookup_eval_indexes_partial_point.0[3 + index_diff..5 + index_diff])
                .into_iter(),
            [
                dot_product_logup_star_indexes_inner_value_a,
                dot_product_logup_star_indexes_inner_value_b,
                dot_product_logup_star_indexes_inner_value_res,
                EF::ZERO,
            ]
            .into_iter(),
        );

        let mut dot_product_indexes_inner_evals_incr = vec![EF::ZERO; 8];
        for (i, value) in dot_product_indexes_inner_evals_incr
            .iter_mut()
            .enumerate()
            .take(DIMENSION)
        {
            *value = dot_product_logup_star_indexes_inner_value
                + EF::from_usize(i)
                    * [F::ONE, F::ONE, F::ONE, F::ZERO].evaluate(&MultilinearPoint(
                        mem_lookup_eval_indexes_partial_point.0[3 + index_diff..5 + index_diff]
                            .to_vec(),
                    ));
        }
        if dot_product_indexes_inner_evals_incr.evaluate(&MultilinearPoint(
            mem_lookup_eval_indexes_partial_point.0[index_diff..3 + index_diff].to_vec(),
        )) != mem_lookup_eval_spread_indexes_dot_product
        {
            return Err(ProofError::InvalidProof);
        }
    }

    let global_statements_base = packed_pcs_global_statements_for_verifier(
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            vec![
                memory_statements,
                vec![
                    exec_evals_to_verify[COL_INDEX_PC.index_in_air()].clone(),
                    bytecode_logup_star_statements.on_indexes.clone(),
                    initial_pc_statement,
                    final_pc_statement,
                ], // pc
                vec![
                    exec_evals_to_verify[COL_INDEX_FP.index_in_air()].clone(),
                    grand_product_fp_statement,
                ], // fp
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_A.index_in_air()].clone(),
                    Evaluation::new(
                        mem_lookup_eval_indexes_partial_point.clone(),
                        mem_lookup_eval_indexes_a,
                    ),
                ], // exec memory address A
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_B.index_in_air()].clone(),
                    Evaluation::new(
                        mem_lookup_eval_indexes_partial_point.clone(),
                        mem_lookup_eval_indexes_b,
                    ),
                ], // exec memory address B
                vec![
                    exec_evals_to_verify[COL_INDEX_MEM_ADDRESS_C.index_in_air()].clone(),
                    Evaluation::new(
                        mem_lookup_eval_indexes_partial_point,
                        mem_lookup_eval_indexes_c,
                    ),
                ], // exec memory address C
                p16_indexes_a_statements,
                p16_indexes_b_statements,
                p16_indexes_res_statements,
                p24_indexes_a_statements,
                p24_indexes_b_statements,
                p24_indexes_res_statements,
            ],
            p16_evals_to_verify[16..p16_air.width() - 16]
                .iter()
                .map(|e| vec![e.clone()])
                .collect(),
            p24_evals_to_verify[24..p24_air.width() - 24]
                .iter()
                .map(|e| vec![e.clone()])
                .collect(),
            vec![
                vec![
                    dot_product_evals_to_verify[0].clone(),
                    grand_product_dot_product_flag_statement,
                ], // dot product: (start) flag
                vec![
                    dot_product_evals_to_verify[1].clone(),
                    grand_product_dot_product_len_statement,
                ], // dot product: length
                vec![
                    dot_product_evals_to_verify[2].clone(), // // dot product: indexe a
                    dot_product_logup_star_indexes_statement_a,
                    grand_product_dot_product_table_indexes_statement_index_a,
                ],
                vec![
                    dot_product_evals_to_verify[3].clone(), // // dot product: indexe b
                    dot_product_logup_star_indexes_statement_b,
                    grand_product_dot_product_table_indexes_statement_index_b,
                ],
                vec![
                    dot_product_evals_to_verify[4].clone(), // // dot product: indexe res
                    dot_product_logup_star_indexes_statement_res,
                    grand_product_dot_product_table_indexes_statement_index_res,
                ],
            ],
            dot_product_computation_column_statements,
        ]
        .concat(),
        &mut verifier_state,
        &[(0, public_memory.clone())].into_iter().collect(),
    )?;

    let global_statements_extension = packed_pcs_global_statements_for_verifier(
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            base_memory_logup_star_statements.on_pushforward,
            poseidon_logup_star_statements.on_pushforward,
            bytecode_logup_star_statements.on_pushforward,
        ],
        &mut verifier_state,
        &Default::default(),
    )?;

    WhirConfig::new(whir_config_builder, parsed_commitment_base.num_variables).batch_verify(
        &mut verifier_state,
        &parsed_commitment_base,
        global_statements_base,
        &parsed_commitment_extension,
        global_statements_extension,
    )?;

    Ok(())
}
