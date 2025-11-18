use crate::common::*;
use crate::*;
use ::air::AirTable;
use air::verify_air;
use lean_vm::*;
use lookup::verify_gkr_quotient;
use lookup::verify_logup_star;
use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use poseidon_circuit::PoseidonGKRLayers;
use poseidon_circuit::verify_poseidon_gkr;
use sub_protocols::*;
use utils::ToUsize;
use utils::{build_challenger, padd_with_zero_to_next_power_of_two};
use vm_air::*;
use whir_p3::WhirConfig;
use whir_p3::WhirConfigBuilder;
use whir_p3::second_batched_whir_config_builder;

pub fn verify_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    proof_data: Vec<PF<EF>>,
    whir_config_builder: WhirConfigBuilder,
) -> Result<(), ProofError> {
    let mut verifier_state = VerifierState::new(proof_data, build_challenger());

    let p16_gkr_layers = PoseidonGKRLayers::<16, N_COMMITED_CUBES_P16>::build(Some(VECTOR_LEN));
    let p24_gkr_layers = PoseidonGKRLayers::<24, N_COMMITED_CUBES_P24>::build(None);

    let [
        n_cycles,
        n_poseidons_16,
        n_compressions_16,
        n_poseidons_24,
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

    if n_compressions_16
        > n_poseidons_16
            .next_power_of_two()
            .max(1 << LOG_MIN_POSEIDONS_16)
        || n_vm_multilinear_evals > 1 << 10
    {
        return Err(ProofError::InvalidProof);
    }

    let public_memory = build_public_memory(public_input);

    let log_public_memory = log2_strict_usize(public_memory.len());
    let log_memory = log2_ceil_usize(public_memory.len() + private_memory_len);
    let log_n_p16 = log2_ceil_usize(n_poseidons_16).max(LOG_MIN_POSEIDONS_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24).max(LOG_MIN_POSEIDONS_24);
    let log_n_cycles = log2_ceil_usize(n_cycles);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let table_dot_products_log_n_rows =
        log2_ceil_usize(n_rows_table_dot_products).max(LOG_MIN_DOT_PRODUCT_ROWS);
    let dot_product_padding_len = (1 << table_dot_products_log_n_rows) - n_rows_table_dot_products;

    let mut vm_multilinear_evals = Vec::new();
    for _ in 0..n_vm_multilinear_evals {
        let [addr_coeffs, addr_point, addr_res, n_vars] =
            verifier_state.next_base_scalars_const::<4>()?;
        let point = verifier_state.next_extension_scalars_vec(n_vars.to_usize())?;
        let res = verifier_state.next_extension_scalar()?;
        vm_multilinear_evals.push(RowMultilinearEval {
            addr_coeffs: addr_coeffs.to_usize(),
            addr_point: addr_point.to_usize(),
            addr_res: addr_res.to_usize(),
            point,
            res,
        });
    }

    let mut memory_statements = vec![];
    for entry in &vm_multilinear_evals {
        add_memory_statements_for_dot_product_precompile(
            entry,
            log_memory,
            log_public_memory,
            &mut verifier_state,
            &mut memory_statements,
        )?;
    }

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory_len,
        bytecode.ending_pc,
        (n_poseidons_16, n_poseidons_24),
        n_rows_table_dot_products,
        (&p16_gkr_layers, &p24_gkr_layers),
    );

    let parsed_commitment_base = packed_pcs_parse_commitment(
        &whir_config_builder,
        &mut verifier_state,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )?;

    let bus_challenge = verifier_state.sample();
    let fingerprint_challenge = verifier_state.sample();

    let (exec_bus_quotient, exec_bus_beta, exec_bus_virtual_statement) = {
        let (exec_bus_quotient, exec_bus_point, exec_bus_selector_value, exec_bus_data_value) =
            verify_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(&mut verifier_state, log_n_cycles)?;
        let exec_bus_beta = verifier_state.sample();
        let exec_bus_final_value = exec_bus_selector_value + exec_bus_beta * exec_bus_data_value;

        let exec_bus_virtual_statement =
            MultiEvaluation::new(exec_bus_point, vec![exec_bus_final_value]);
        (exec_bus_quotient, exec_bus_beta, exec_bus_virtual_statement)
    };

    let (
        p16_bus_quotient,
        p16_bus_point,
        p16_bus_eval_index_input_a,
        p16_bus_eval_index_input_b,
        p16_bus_eval_index_input_output,
    ) = {
        let (p16_bus_quotient, p16_bus_point, p16_bus_selector_value, p16_bus_data_value) =
            verify_gkr_quotient::<_, 2>(&mut verifier_state, log_n_p16)?;
        let [
            p16_bus_eval_index_input_a,
            p16_bus_eval_index_input_b,
            p16_bus_eval_index_input_output,
        ] = verifier_state.next_extension_scalars_const::<3>()?;

        if p16_bus_selector_value
            != mle_of_zeros_then_ones(n_poseidons_16, &p16_bus_point) - EF::ONE
        {
            return Err(ProofError::InvalidProof);
        }

        let p16_eval_on_compression =
            mle_of_zeros_then_ones((1 << log_n_p16) - n_compressions_16, &p16_bus_point);

        if p16_bus_data_value
            != bus_challenge
                + finger_print(
                    TABLE_INDEX_POSEIDONS_16,
                    &[
                        p16_bus_eval_index_input_a,
                        p16_bus_eval_index_input_b,
                        p16_bus_eval_index_input_output,
                        p16_eval_on_compression,
                    ],
                    fingerprint_challenge,
                )
        {
            return Err(ProofError::InvalidProof);
        }

        (
            p16_bus_quotient,
            p16_bus_point,
            p16_bus_eval_index_input_a,
            p16_bus_eval_index_input_b,
            p16_bus_eval_index_input_output,
        )
    };

    let (
        p24_bus_quotient,
        p24_bus_point,
        p24_bus_eval_index_input_a,
        p24_bus_eval_index_input_b,
        p24_bus_eval_index_input_output,
    ) = {
        let (p24_bus_quotient, p24_bus_point, p24_bus_selector_value, p24_bus_data_value) =
            verify_gkr_quotient::<_, 2>(&mut verifier_state, log_n_p24)?;
        let [
            p24_bus_eval_index_input_a,
            p24_bus_eval_index_input_b,
            p24_bus_eval_index_input_output,
        ] = verifier_state.next_extension_scalars_const::<3>()?;

        if p24_bus_selector_value
            != mle_of_zeros_then_ones(n_poseidons_24, &p24_bus_point) - EF::ONE
        {
            return Err(ProofError::InvalidProof);
        }

        if p24_bus_data_value
            != bus_challenge
                + finger_print(
                    TABLE_INDEX_POSEIDONS_24,
                    &[
                        p24_bus_eval_index_input_a,
                        p24_bus_eval_index_input_b,
                        p24_bus_eval_index_input_output,
                    ],
                    fingerprint_challenge,
                )
        {
            return Err(ProofError::InvalidProof);
        }

        (
            p24_bus_quotient,
            p24_bus_point,
            p24_bus_eval_index_input_a,
            p24_bus_eval_index_input_b,
            p24_bus_eval_index_input_output,
        )
    };

    let (mut dot_product_bus_quotient, dot_product_bus_beta, dot_product_bus_virtual_statement) = {
        let (
            dot_product_bus_quotient,
            dot_product_bus_point,
            dot_product_bus_selector_value,
            dot_product_bus_data_value,
        ) = verify_gkr_quotient::<_, 2>(&mut verifier_state, table_dot_products_log_n_rows)?;
        let dot_product_bus_beta = verifier_state.sample();
        let dot_product_bus_final_value =
            (-dot_product_bus_selector_value) + dot_product_bus_beta * dot_product_bus_data_value; // Note the "-" sign here !!

        let dot_product_bus_virtual_statement =
            MultiEvaluation::new(dot_product_bus_point, vec![dot_product_bus_final_value]);
        (
            dot_product_bus_quotient,
            dot_product_bus_beta,
            dot_product_bus_virtual_statement,
        )
    };

    let multilinear_eval_bus_quotient = vm_multilinear_evals
        .par_iter()
        .map(|vm_multilinear_eval| {
            -EF::ONE
                / (bus_challenge
                    + finger_print(
                        TABLE_INDEX_MULTILINEAR_EVAL,
                        &vm_multilinear_eval.addresses_and_n_vars_field_repr(),
                        fingerprint_challenge,
                    ))
        })
        .sum::<EF>();

    dot_product_bus_quotient += EF::from_usize(dot_product_padding_len)
        / (bus_challenge
            + finger_print(
                TABLE_INDEX_DOT_PRODUCTS,
                &[
                    EF::ZERO, // IndexA
                    EF::ZERO, // IndexB
                    EF::ZERO, // IndexRes
                    EF::ONE,  // Len
                ],
                fingerprint_challenge,
            ));
    if exec_bus_quotient
        + p16_bus_quotient
        + p24_bus_quotient
        + dot_product_bus_quotient
        + multilinear_eval_bus_quotient
        != EF::ZERO
    {
        return Err(ProofError::InvalidProof);
    }

    let mut p16_indexes_a_statements = vec![Evaluation::new(
        p16_bus_point.clone(),
        p16_bus_eval_index_input_a,
    )];
    let mut p16_indexes_b_statements = vec![Evaluation::new(
        p16_bus_point.clone(),
        p16_bus_eval_index_input_b,
    )];
    let mut p16_indexes_res_statements = vec![Evaluation::new(
        p16_bus_point.clone(),
        p16_bus_eval_index_input_output,
    )];

    let mut p24_indexes_a_statements = vec![Evaluation::new(
        p24_bus_point.clone(),
        p24_bus_eval_index_input_a,
    )];
    let mut p24_indexes_b_statements = vec![Evaluation::new(
        p24_bus_point.clone(),
        p24_bus_eval_index_input_b,
    )];
    let mut p24_indexes_res_statements = vec![Evaluation::new(
        p24_bus_point.clone(),
        p24_bus_eval_index_input_output,
    )];

    let exec_table = AirTable::<EF, _>::new(VMAir {
        bus_challenge,
        fingerprint_challenge_powers: powers_const(fingerprint_challenge),
        exec_bus_beta,
    });
    let (exec_air_point, exec_evals_to_verify) = verify_air(
        &mut verifier_state,
        &exec_table,
        UNIVARIATE_SKIPS,
        log_n_cycles,
        &execution_air_padding_row::<EF>(bytecode.ending_pc),
        Some(exec_bus_virtual_statement),
    )?;

    let dot_product_table = AirTable::<EF, _>::new(DotProductAir {
        bus_challenge,
        fingerprint_challenge_powers: powers_const(fingerprint_challenge),
        dot_product_bus_beta,
    });
    let (dot_product_air_point, dot_product_evals_to_verify) = verify_air(
        &mut verifier_state,
        &dot_product_table,
        DOT_PRODUCT_UNIVARIATE_SKIPS,
        table_dot_products_log_n_rows,
        &dot_product_air_padding_row(),
        Some(dot_product_bus_virtual_statement),
    )?;

    let random_point_p16 = MultilinearPoint(verifier_state.sample_vec(log_n_p16));
    let p16_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        log_n_p16,
        &random_point_p16,
        &p16_gkr_layers,
        UNIVARIATE_SKIPS,
        Some(n_compressions_16),
    );

    let random_point_p24 = MultilinearPoint(verifier_state.sample_vec(log_n_p24));
    let p24_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        log_n_p24,
        &random_point_p24,
        &p24_gkr_layers,
        UNIVARIATE_SKIPS,
        None,
    );

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_lookup_claim_1 = Evaluation::new(
        exec_air_point.clone(),
        padd_with_zero_to_next_power_of_two(&exec_evals_to_verify[..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );

    let normal_lookup_into_memory = NormalPackedLookupVerifier::step_1(
        &mut verifier_state,
        3,
        [
            vec![n_cycles; 3],
            vec![n_rows_table_dot_products.max(1 << LOG_MIN_DOT_PRODUCT_ROWS); 3],
        ]
        .concat(),
        [vec![0; 3], vec![0; 3]].concat(),
        normal_lookup_into_memory_initial_statements(
            &exec_air_point,
            &exec_evals_to_verify,
            &dot_product_air_point,
            &dot_product_evals_to_verify,
        ),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let vectorized_lookup_into_memory = VectorizedPackedLookupVerifier::<_, VECTOR_LEN>::step_1(
        &mut verifier_state,
        [
            vec![n_poseidons_16.max(1 << LOG_MIN_POSEIDONS_16); 4],
            vec![n_poseidons_24.max(1 << LOG_MIN_POSEIDONS_24); 4],
        ]
        .concat(),
        default_poseidon_indexes(),
        poseidon_lookup_statements(&p16_gkr, &p24_gkr),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let extension_dims = vec![
        ColDims::padded(public_memory.len() + private_memory_len, EF::ZERO), // memory pushwordard
        ColDims::padded(
            (public_memory.len() + private_memory_len).div_ceil(VECTOR_LEN),
            EF::ZERO,
        ), // memory (folded) pushwordard
        ColDims::padded(bytecode.instructions.len(), EF::ZERO),              // bytecode pushforward
    ];

    let parsed_commitment_extension = packed_pcs_parse_commitment(
        &second_batched_whir_config_builder(
            whir_config_builder.clone(),
            parsed_commitment_base.num_variables,
            num_packed_vars_for_dims::<EF>(&extension_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK),
        ),
        &mut verifier_state,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    )?;

    let normal_lookup_statements =
        normal_lookup_into_memory.step_2(&mut verifier_state, log_memory)?;

    let vectorized_lookup_statements =
        vectorized_lookup_into_memory.step_2(&mut verifier_state, log_memory)?;

    let bytecode_logup_star_statements = verify_logup_star(
        &mut verifier_state,
        log2_ceil_usize(bytecode.instructions.len()),
        log_n_cycles,
        &[bytecode_lookup_claim_1],
        EF::ONE,
    )?;
    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);
    if folded_bytecode.evaluate(&bytecode_logup_star_statements.on_table.point)
        != bytecode_logup_star_statements.on_table.value
    {
        return Err(ProofError::InvalidProof);
    }

    memory_statements.push(normal_lookup_statements.on_table.clone());
    memory_statements.push(vectorized_lookup_statements.on_table.clone());

    {
        // index opening for poseidon lookup

        // index opening for poseidon lookup
        p16_indexes_a_statements.extend(vectorized_lookup_statements.on_indexes[0].clone());
        p16_indexes_b_statements.extend(vectorized_lookup_statements.on_indexes[1].clone());
        p16_indexes_res_statements.extend(vectorized_lookup_statements.on_indexes[2].clone());
        // vectorized_lookup_statements.on_indexes[3] is proven via sumcheck below
        p24_indexes_a_statements.extend(vectorized_lookup_statements.on_indexes[4].clone());
        p24_indexes_a_statements.extend(
            vectorized_lookup_statements.on_indexes[5]
                .iter()
                .map(|eval| Evaluation::new(eval.point.clone(), eval.value - EF::ONE)),
        );
        p24_indexes_b_statements.extend(vectorized_lookup_statements.on_indexes[6].clone());
        p24_indexes_res_statements.extend(vectorized_lookup_statements.on_indexes[7].clone());

        let alpha = verifier_state.sample();

        let (p16_value_index_res_b, sc_eval) = sumcheck_verify_with_univariate_skip(
            &mut verifier_state,
            3,
            log_n_p16,
            1, // TODO univariate skip
        )?;
        let mut eq_poly_eval = EF::ZERO;
        let mut p16_value_index_res_b_expected = EF::ZERO;
        for (statement, alpha_power) in vectorized_lookup_statements.on_indexes[3]
            .iter()
            .zip(alpha.powers())
        {
            p16_value_index_res_b_expected += statement.value * alpha_power;
            eq_poly_eval += alpha_power * statement.point.eq_poly_outside(&sc_eval.point);
        }
        if p16_value_index_res_b_expected != p16_value_index_res_b {
            return Err(ProofError::InvalidProof);
        }
        let sc_res_index_value = verifier_state.next_extension_scalar()?;
        p16_indexes_res_statements.push(Evaluation::new(
            sc_eval.point.clone(),
            sc_res_index_value - EF::ONE,
        ));

        if sc_res_index_value
            * (EF::ONE
                - mle_of_zeros_then_ones((1 << log_n_p16) - n_compressions_16, &sc_eval.point))
            * eq_poly_eval
            != sc_eval.value
        {
            return Err(ProofError::InvalidProof);
        }
    }

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_computation_column_statements =
        ExtensionCommitmentFromBaseVerifier::after_commitment(
            &mut verifier_state,
            &Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_evals_to_verify
                    [DOT_PRODUCT_AIR_COL_COMPUTATION + DOT_PRODUCT_AIR_N_COLUMNS_F],
            ),
        )?;

    let exec_air_statement =
        |col_index: usize| Evaluation::new(exec_air_point.clone(), exec_evals_to_verify[col_index]);
    let dot_product_air_statement = |col_index: usize| {
        Evaluation::new(
            dot_product_air_point.clone(),
            dot_product_evals_to_verify[col_index],
        )
    };

    let global_statements_base = packed_pcs_global_statements_for_verifier(
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            vec![
                memory_statements,
                vec![
                    exec_air_statement(COL_INDEX_PC),
                    bytecode_logup_star_statements.on_indexes.clone(),
                    initial_pc_statement,
                    final_pc_statement,
                ], // pc
                vec![exec_air_statement(COL_INDEX_FP)], // fp
                [
                    vec![exec_air_statement(COL_INDEX_MEM_ADDRESS_A)],
                    normal_lookup_statements.on_indexes[0].clone(),
                ]
                .concat(), // exec memory address A
                [
                    vec![exec_air_statement(COL_INDEX_MEM_ADDRESS_B)],
                    normal_lookup_statements.on_indexes[1].clone(),
                ]
                .concat(), // exec memory address B
                [
                    vec![exec_air_statement(COL_INDEX_MEM_ADDRESS_C)],
                    normal_lookup_statements.on_indexes[2].clone(),
                ]
                .concat(), // exec memory address C
                p16_indexes_a_statements,
                p16_indexes_b_statements,
                p16_indexes_res_statements,
                p24_indexes_a_statements,
                p24_indexes_b_statements,
                p24_indexes_res_statements,
            ],
            encapsulate_vec(p16_gkr.cubes_statements.split()),
            encapsulate_vec(p24_gkr.cubes_statements.split()),
            vec![
                vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_START_FLAG)], // dot product: (start) flag
                vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_LEN)], // dot product: length
                [
                    vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_A)],
                    normal_lookup_statements.on_indexes[3].clone(),
                ]
                .concat(),
                [
                    vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_B)],
                    normal_lookup_statements.on_indexes[4].clone(),
                ]
                .concat(),
                [
                    vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_RES)],
                    normal_lookup_statements.on_indexes[4].clone(),
                ]
                .concat(),
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
            normal_lookup_statements.on_pushforward,
            vectorized_lookup_statements.on_pushforward,
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
