use crate::common::*;
use crate::*;
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
        n_poseidons_24,
        n_rows_table_dot_products,
        private_memory_len,
        n_vm_multilinear_evals,
    ] = verifier_state
        .next_base_scalars_const::<6>()?
        .into_iter()
        .map(|x| x.to_usize())
        .collect::<Vec<_>>()
        .try_into()
        .unwrap();

    if n_vm_multilinear_evals > 1 << 10 {
        return Err(ProofError::InvalidProof);
    }

    let public_memory = build_public_memory(public_input);

    let log_public_memory = log2_strict_usize(public_memory.len());
    let log_memory = log2_ceil_usize(public_memory.len() + private_memory_len);
    let log_n_p16 = log2_ceil_usize(n_poseidons_16).max(MIN_LOG_N_ROWS_PER_TABLE);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24).max(MIN_LOG_N_ROWS_PER_TABLE);
    let log_n_cycles = log2_ceil_usize(n_cycles);

    if !(MIN_LOG_MEMORY_SIZE..=MAX_LOG_MEMORY_SIZE).contains(&log_memory) {
        return Err(ProofError::InvalidProof);
    }

    let table_dot_products_log_n_rows =
        log2_ceil_usize(n_rows_table_dot_products).max(MIN_LOG_N_ROWS_PER_TABLE);
    let dot_product_padding_len = (1 << table_dot_products_log_n_rows) - n_rows_table_dot_products;

    let mut vm_multilinear_evals = TableTrace::new(&MultilinearEvalPrecompile);
    let mut multilinear_evals_witness = vec![];
    for _ in 0..n_vm_multilinear_evals {
        let [addr_coeffs, addr_point, addr_res, n_vars] =
            verifier_state.next_base_scalars_const::<4>()?;
        let point = verifier_state.next_extension_scalars_vec(n_vars.to_usize())?;
        let res = verifier_state.next_extension_scalar()?;
        vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_POLY].push(addr_coeffs);
        vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_POINT].push(addr_point);
        vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_RES].push(addr_res);
        vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_N_VARS].push(n_vars);
        multilinear_evals_witness.push(WitnessMultilinearEval { point, res });
    }

    let mut memory_statements = vec![];
    for (row, entry) in multilinear_evals_witness.iter().enumerate() {
        add_memory_statements_for_multilinear_eval_precompile(
            entry,
            &vm_multilinear_evals,
            row,
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

    let random_point_p16 = MultilinearPoint(verifier_state.sample_vec(log_n_p16));
    let p16_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        log_n_p16,
        &random_point_p16,
        &p16_gkr_layers,
        UNIVARIATE_SKIPS,
        true,
    );

    let random_point_p24 = MultilinearPoint(verifier_state.sample_vec(log_n_p24));
    let p24_gkr = verify_poseidon_gkr(
        &mut verifier_state,
        log_n_p24,
        &random_point_p24,
        &p24_gkr_layers,
        UNIVARIATE_SKIPS,
        false,
    );

    let bus_challenge = verifier_state.sample();
    let fingerprint_challenge = verifier_state.sample();

    let (exec_bus_quotient, exec_bus_beta, exec_bus_virtual_statement) =
        process_bus_quotient::<TWO_POW_UNIVARIATE_SKIPS>(
            &mut verifier_state,
            log_n_cycles,
            Table::execution().buses()[0].direction,
        )?; // TODO multiple buses

    let (p16_bus_quotient, p16_bus_beta, p16_bus_virtual_statement) =
        process_bus_quotient::<TWO_POW_UNIVARIATE_SKIPS>(
            &mut verifier_state,
            log_n_p16,
            Table::poseidon16().buses()[0].direction,
        )?; // TODO multiple buses

    let (p24_bus_quotient, p24_bus_beta, p24_bus_virtual_statement) =
        process_bus_quotient::<TWO_POW_UNIVARIATE_SKIPS>(
            &mut verifier_state,
            log_n_p24,
            Table::poseidon24().buses()[0].direction,
        )?; // TODO multiple buses
    let (mut dot_product_bus_quotient, dot_product_bus_beta, dot_product_bus_virtual_statement) =
        process_bus_quotient::<TWO_POW_UNIVARIATE_SKIPS>(
            &mut verifier_state,
            table_dot_products_log_n_rows,
            Table::dot_product().buses()[0].direction,
        )?; // TODO multiple buses

    let multilinear_eval_bus_quotient = (0..multilinear_evals_witness.len())
        .map(|row| {
            -EF::ONE
                / (bus_challenge
                    + finger_print(
                        Table::multilinear_eval().embed(),
                        &[
                            vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_POLY][row],
                            vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_POINT][row],
                            vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_RES][row],
                            vm_multilinear_evals.base[MULTILINEAR_EVAL_COL_INDEX_N_VARS][row],
                        ],
                        fingerprint_challenge,
                    ))
        })
        .sum::<EF>();

    dot_product_bus_quotient += EF::from_usize(dot_product_padding_len)
        / (bus_challenge
            + finger_print(
                Table::dot_product().embed(),
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

    let (exec_air_point, exec_evals_to_verify_f, exec_evals_to_verify_ef) = verify_table_air(
        &mut verifier_state,
        &ExecutionTable,
        log_n_cycles,
        bus_challenge,
        fingerprint_challenge,
        exec_bus_beta,
        Some(exec_bus_virtual_statement),
    )?;

    let (dot_product_air_point, dot_product_evals_to_verify_f, dot_product_evals_to_verify_ef) =
        verify_table_air(
            &mut verifier_state,
            &DotProductPrecompile,
            table_dot_products_log_n_rows,
            bus_challenge,
            fingerprint_challenge,
            dot_product_bus_beta,
            Some(dot_product_bus_virtual_statement),
        )?;

    let (p16_air_point, p16_evals_to_prove_f, p16_evals_to_prove_ef) = verify_table_air(
        &mut verifier_state,
        &Poseidon16Precompile,
        log_n_p16,
        bus_challenge,
        fingerprint_challenge,
        p16_bus_beta,
        Some(p16_bus_virtual_statement),
    )?;
    let (p24_air_point, p24_evals_to_prove_f, p24_evals_to_prove_ef) = verify_table_air(
        &mut verifier_state,
        &Poseidon24Precompile,
        log_n_p24,
        bus_challenge,
        fingerprint_challenge,
        p24_bus_beta,
        Some(p24_bus_virtual_statement),
    )?;

    let bytecode_compression_challenges =
        MultilinearPoint(verifier_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let bytecode_lookup_claim_1 = Evaluation::new(
        exec_air_point.clone(),
        padd_with_zero_to_next_power_of_two(&exec_evals_to_verify_f[..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );

    let normal_lookup_into_memory = NormalPackedLookupVerifier::step_1(
        &mut verifier_state,
        [
            vec![n_cycles; Table::execution().num_normal_lookups_f()],
            vec![
                n_rows_table_dot_products.max(MIN_N_ROWS_PER_TABLE);
                Table::dot_product().num_normal_lookups_f()
            ],
        ]
        .concat(),
        [
            vec![n_cycles; Table::execution().num_normal_lookups_ef()],
            vec![
                n_rows_table_dot_products.max(MIN_N_ROWS_PER_TABLE);
                Table::dot_product().num_normal_lookups_ef()
            ],
        ]
        .concat(),
        [
            vec![0; Table::execution().num_normal_lookups_f()],
            vec![0; Table::dot_product().num_normal_lookups_f()],
        ]
        .concat(), // TODO handle the case with non-zero default index
        [
            vec![0; Table::execution().num_normal_lookups_ef()],
            vec![0; Table::dot_product().num_normal_lookups_ef()],
        ]
        .concat(), // TODO handle the case with non-zero default index
        [
            Table::execution()
                .normal_lookups_statements_f(&exec_air_point, &exec_evals_to_verify_f),
            Table::dot_product().normal_lookups_statements_f(
                &dot_product_air_point,
                &dot_product_evals_to_verify_f,
            ),
        ]
        .concat(),
        [
            Table::execution()
                .normal_lookups_statements_ef(&exec_air_point, &exec_evals_to_verify_ef),
            Table::dot_product().normal_lookups_statements_ef(
                &dot_product_air_point,
                &dot_product_evals_to_verify_ef,
            ),
        ]
        .concat(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &public_memory, // we need to pass the first few values of memory, public memory is enough
    )?;

    let vectorized_lookup_into_memory = VectorizedPackedLookupVerifier::<_, VECTOR_LEN>::step_1(
        &mut verifier_state,
        [
            vec![
                n_poseidons_16.max(MIN_N_ROWS_PER_TABLE);
                Table::poseidon16().num_vector_lookups()
            ],
            vec![
                n_poseidons_24.max(MIN_N_ROWS_PER_TABLE);
                Table::poseidon24().num_vector_lookups()
            ],
        ]
        .concat(),
        [
            Table::poseidon16().vector_lookup_default_indexes(),
            Table::poseidon24().vector_lookup_default_indexes(),
        ]
        .concat(),
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

    let mut normal_lookup_statements =
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

    let mut p16_statements = Table::poseidon16().committed_statements_verifier(
        &mut verifier_state,
        &p16_air_point,
        &p16_evals_to_prove_f,
        &p16_evals_to_prove_ef,
        &mut vec![],
        &mut vec![],
    )?;
    let mut p24_statements = Table::poseidon24().committed_statements_verifier(
        &mut verifier_state,
        &p24_air_point,
        &p24_evals_to_prove_f,
        &p24_evals_to_prove_ef,
        &mut vec![],
        &mut vec![],
    )?;
    {
        // index opening for poseidon lookup
        for (i, statement) in vectorized_lookup_statements.on_indexes[..4]
            .iter()
            .enumerate()
        {
            // TODO be more general
            p16_statements[Poseidon16Precompile.vector_lookups()[i].index]
                .extend(statement.clone());
        }
        for (i, statement) in vectorized_lookup_statements.on_indexes[4..]
            .iter()
            .enumerate()
        {
            // TODO be more general
            p24_statements[Poseidon24Precompile.vector_lookups()[i].index]
                .extend(statement.clone());
        }
    }

    let (initial_pc_statement, final_pc_statement) = initial_and_final_pc_conditions(log_n_cycles);

    let dot_product_statements = DotProductPrecompile.committed_statements_verifier(
        &mut verifier_state,
        &dot_product_air_point,
        &dot_product_evals_to_verify_f,
        &dot_product_evals_to_verify_ef,
        &mut normal_lookup_statements.on_indexes_f,
        &mut normal_lookup_statements.on_indexes_ef,
    )?;

    let mut exec_statements = Table::execution().committed_statements_verifier(
        &mut verifier_state,
        &exec_air_point,
        &exec_evals_to_verify_f,
        &exec_evals_to_verify_ef,
        &mut normal_lookup_statements.on_indexes_f,
        &mut normal_lookup_statements.on_indexes_ef,
    )?;
    exec_statements[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)].extend(vec![
        bytecode_logup_star_statements.on_indexes.clone(),
        initial_pc_statement,
        final_pc_statement,
    ]);

    let global_statements_base = packed_pcs_global_statements_for_verifier(
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            vec![memory_statements],
            exec_statements,
            p16_statements,
            encapsulate_vec(p16_gkr.cubes_statements.split()),
            p24_statements,
            encapsulate_vec(p24_gkr.cubes_statements.split()),
            dot_product_statements,
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

fn process_bus_quotient<const TWO_POW_UNIVARIATE_SKIPS: usize>(
    verifier_state: &mut VerifierState<PF<EF>, EF, impl FSChallenger<EF>>,
    log_n: usize,
    bus_direction: BusDirection,
) -> ProofResult<(EF, EF, MultiEvaluation<EF>)> {
    let (quotient, point, selector_value, data_value) =
        verify_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(verifier_state, log_n)?;

    let beta = verifier_state.sample();

    let final_value = selector_value * bus_direction.to_field_flag() + beta * data_value;

    let virtual_statement = MultiEvaluation::new(point, vec![final_value]);

    Ok((quotient, beta, virtual_statement))
}

fn verify_table_air<T: TableT<ExtraData = ExtraDataForBuses<EF>>>(
    verifier_state: &mut VerifierState<PF<EF>, EF, impl FSChallenger<EF>>,
    t: &T,
    log_n_rows: usize,
    bus_challenge: EF,
    fingerprint_challenge: EF,
    bus_beta: EF,
    bus_virtual_statement: Option<MultiEvaluation<EF>>,
) -> ProofResult<(MultilinearPoint<EF>, Vec<EF>, Vec<EF>)> {
    let air_extra_data = ExtraDataForBuses {
        bus_challenge,
        fingerprint_challenge_powers: powers_const(fingerprint_challenge),
        bus_beta,
        alpha_powers: vec![], // filled later
    };
    verify_air(
        verifier_state,
        t,
        air_extra_data,
        UNIVARIATE_SKIPS,
        log_n_rows,
        &t.air_padding_row_f(),
        &t.air_padding_row_ef(),
        bus_virtual_statement,
    )
}
