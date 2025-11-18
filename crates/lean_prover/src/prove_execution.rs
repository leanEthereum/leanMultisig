use std::array;

use crate::common::*;
use crate::*;
use ::air::AirTable;
use air::prove_air;
use lean_vm::*;
use lookup::{compute_pushforward, prove_gkr_quotient, prove_logup_star};
use multilinear_toolkit::prelude::*;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use poseidon_circuit::{PoseidonGKRLayers, prove_poseidon_gkr};
use sub_protocols::*;
use tracing::info_span;
use utils::{build_prover_state, padd_with_zero_to_next_power_of_two};
use vm_air::*;
use whir_p3::{
    WhirConfig, WhirConfigBuilder, precompute_dft_twiddles, second_batched_whir_config_builder,
};
use xmss::{Poseidon16History, Poseidon24History};

pub fn prove_execution(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    whir_config_builder: WhirConfigBuilder,
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    vm_profiler: bool,
    (poseidons_16_precomputed, poseidons_24_precomputed): (&Poseidon16History, &Poseidon24History),
) -> (Vec<PF<EF>>, usize, String) {
    let mut exec_summary = String::new();
    let ExecutionTrace {
        full_trace,
        nu_columns,
        n_cycles,
        n_poseidons_16,
        n_poseidons_24,
        poseidons_16,      // padded with empty poseidons
        poseidons_24,      // padded with empty poseidons
        n_compressions_16, // included the padding (that are compressions of zeros)
        dot_products,
        multilinear_evals: vm_multilinear_evals,
        public_memory_size,
        mut non_zero_memory_size,
        mut memory, // padded with zeros to next power of two
    } = info_span!("Witness generation").in_scope(|| {
        let mut execution_result = info_span!("Executing bytecode").in_scope(|| {
            execute_bytecode(
                bytecode,
                (public_input, private_input),
                no_vec_runtime_memory,
                vm_profiler,
                (poseidons_16_precomputed, poseidons_24_precomputed),
            )
        });
        exec_summary = std::mem::take(&mut execution_result.summary);
        info_span!("Building execution trace")
            .in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    if memory.len() < 1 << MIN_LOG_MEMORY_SIZE {
        memory.resize(1 << MIN_LOG_MEMORY_SIZE, F::ZERO);
        non_zero_memory_size = 1 << MIN_LOG_MEMORY_SIZE;
    }
    let public_memory = &memory[..public_memory_size];
    let private_memory = &memory[public_memory_size..non_zero_memory_size];
    let log_memory = log2_strict_usize(memory.len());
    let log_public_memory = log2_strict_usize(public_memory.len());

    let log_n_cycles = log2_ceil_usize(n_cycles);
    assert!(full_trace.iter().all(|col| col.len() == 1 << log_n_cycles));

    let log_n_p16 = log2_ceil_usize(n_poseidons_16).max(LOG_MIN_POSEIDONS_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24).max(LOG_MIN_POSEIDONS_24);

    precompute_dft_twiddles::<F>(1 << 24);

    let _validity_proof_span = info_span!("Validity proof generation").entered();

    let p16_gkr_layers = PoseidonGKRLayers::<16, N_COMMITED_CUBES_P16>::build(Some(VECTOR_LEN));
    let p24_gkr_layers = PoseidonGKRLayers::<24, N_COMMITED_CUBES_P24>::build(None);

    let p16_witness =
        generate_poseidon_witness_helper(&p16_gkr_layers, &poseidons_16, Some(n_compressions_16));
    let p24_witness = generate_poseidon_witness_helper(&p24_gkr_layers, &poseidons_24, None);

    let DotProductColumns {
        in_base: dot_product_columns_f,
        in_ext: dot_product_columns_ef,
        padding_len: dot_product_padding_len,
    } = build_dot_product_columns(&dot_products, 1 << LOG_MIN_DOT_PRODUCT_ROWS);

    let dot_product_computation_ext_to_base_helper =
        ExtensionCommitmentFromBaseProver::before_commitment(
            &dot_product_columns_ef[DOT_PRODUCT_AIR_COL_COMPUTATION],
        );

    let n_rows_table_dot_products = dot_product_columns_f[0].len() - dot_product_padding_len;
    let log_n_rows_dot_product_table = log2_strict_usize(dot_product_columns_f[0].len());

    let mut prover_state = build_prover_state::<EF>();
    prover_state.add_base_scalars(
        &[
            n_cycles,
            n_poseidons_16,
            n_compressions_16,
            n_poseidons_24,
            n_rows_table_dot_products,
            private_memory.len(),
            vm_multilinear_evals.len(),
        ]
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );

    for vm_multilinear_eval in &vm_multilinear_evals {
        prover_state.add_base_scalars(&[
            F::from_usize(vm_multilinear_eval.addr_coeffs),
            F::from_usize(vm_multilinear_eval.addr_point),
            F::from_usize(vm_multilinear_eval.addr_res),
            F::from_usize(vm_multilinear_eval.n_vars()),
        ]);
        prover_state.add_extension_scalars(&vm_multilinear_eval.point);
        prover_state.add_extension_scalar(vm_multilinear_eval.res);
    }

    let mut memory_statements = vec![];
    for entry in &vm_multilinear_evals {
        add_memory_statements_for_dot_product_precompile(
            entry,
            log_memory,
            log_public_memory,
            &mut prover_state,
            &mut memory_statements,
        )
        .unwrap();
    }
    let [
        p16_indexes_input_a,
        p16_indexes_input_b,
        p16_indexes_output,
        p16_indexes_output_shifted, // = if compressed { 0 } else { p16_indexes_output + 1 }
    ] = all_poseidon_16_indexes(&poseidons_16);
    let [
        p24_indexes_input_a,
        p24_indexes_input_a_shifted, // = p24_indexes_input_a + 1
        p24_indexes_input_b,
        p24_indexes_output,
    ] = all_poseidon_24_indexes(&poseidons_24);

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory.len(),
        bytecode.ending_pc,
        (n_poseidons_16, n_poseidons_24),
        n_rows_table_dot_products,
        (&p16_gkr_layers, &p24_gkr_layers),
    );

    let base_pols = [
        vec![
            memory.as_slice(),
            full_trace[COL_INDEX_PC].as_slice(),
            full_trace[COL_INDEX_FP].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_A].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_B].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_C].as_slice(),
        ],
        vec![
            &p16_indexes_input_a,
            &p16_indexes_input_b,
            &p16_indexes_output,
        ],
        vec![
            &p24_indexes_input_a,
            &p24_indexes_input_b,
            &p24_indexes_output,
        ],
        p16_witness
            .committed_cubes
            .iter()
            .map(|s| FPacking::<F>::unpack_slice(s))
            .collect::<Vec<_>>(),
        p24_witness
            .committed_cubes
            .iter()
            .map(|s| FPacking::<F>::unpack_slice(s))
            .collect::<Vec<_>>(),
        dot_product_columns_f.iter().map(Vec::as_slice).collect(),
        dot_product_computation_ext_to_base_helper
            .sub_columns_to_commit
            .iter()
            .map(Vec::as_slice)
            .collect(),
    ]
    .concat();

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(
        &whir_config_builder,
        &base_pols,
        &base_dims,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let bus_challenge = prover_state.sample();
    let fingerprint_challenge = prover_state.sample();
    let (exec_bus_quotient, exec_bus_beta, exec_bus_virtual_statement) = {
        let mut exec_bus_data = unsafe { uninitialized_vec::<EF>(n_cycles.next_power_of_two()) };

        exec_bus_data.par_iter_mut().enumerate().for_each(|(i, v)| {
            let precompile_index = full_trace[COL_INDEX_PRECOMPILE_INDEX][i];

            *v = bus_challenge
                + finger_print(
                    precompile_index.to_usize(),
                    &[
                        nu_columns[0][i],
                        nu_columns[1][i],
                        nu_columns[2][i],
                        full_trace[COL_INDEX_AUX][i],
                    ],
                    fingerprint_challenge,
                )
        });

        let exec_bus_selector = full_trace[COL_INDEX_IS_PRECOMPILE]
            .par_iter()
            .map(|&v| EF::from(v)) // TODO !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
            .collect::<Vec<_>>();
        let exec_bus_selector_packed = pack_extension(&exec_bus_selector);
        let exec_bus_data_packed = pack_extension(&exec_bus_data);
        let (exec_bus_quotient, exec_bus_point, exec_bus_selector_value, exec_bus_data_value) =
            prove_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(
                &mut prover_state,
                &MleGroupRef::ExtensionPacked(vec![
                    &exec_bus_selector_packed,
                    &exec_bus_data_packed,
                ]),
            );

        let exec_bus_beta = prover_state.sample();
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
        let p16_bus_data = poseidons_16
            .par_iter()
            .map(|pos_16| {
                bus_challenge
                    + finger_print(
                        TABLE_INDEX_POSEIDONS_16,
                        &pos_16.addresses_field_repr(),
                        fingerprint_challenge,
                    )
            })
            .collect::<Vec<_>>();

        let mut p16_bus_selector = vec![-EF::ONE; n_poseidons_16]; // TODO embedding overhead !!!!!!!!!!!!!!
        p16_bus_selector.resize(1 << log_n_p16, EF::ZERO);
        let p16_bus_selector_packed = pack_extension(&p16_bus_selector);
        let p16_bus_data_packed = pack_extension(&p16_bus_data);
        let (p16_bus_quotient, p16_bus_point, _, _) = prove_gkr_quotient::<_, 2>(
            &mut prover_state,
            &MleGroupRef::ExtensionPacked(vec![&p16_bus_selector_packed, &p16_bus_data_packed]),
        );
        let p16_bus_eval_index_input_a = p16_indexes_input_a.evaluate(&p16_bus_point);
        let p16_bus_eval_index_input_b = p16_indexes_input_b.evaluate(&p16_bus_point);
        let p16_bus_eval_index_input_output = p16_indexes_output.evaluate(&p16_bus_point);
        prover_state.add_extension_scalars(&[
            p16_bus_eval_index_input_a,
            p16_bus_eval_index_input_b,
            p16_bus_eval_index_input_output,
        ]);
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
        let p24_bus_data = poseidons_24
            .par_iter()
            .map(|pos_24| {
                bus_challenge
                    + finger_print(
                        TABLE_INDEX_POSEIDONS_24,
                        &pos_24.addresses_field_repr(),
                        fingerprint_challenge,
                    )
            })
            .collect::<Vec<_>>();

        let mut p24_bus_selector = vec![-EF::ONE; n_poseidons_24]; // TODO embedding overhead !!!!!!!!!!!!!!
        p24_bus_selector.resize(1 << log_n_p24, EF::ZERO);
        let p24_bus_selector_packed = pack_extension(&p24_bus_selector);
        let p24_bus_data_packed = pack_extension(&p24_bus_data);
        let (p24_bus_quotient, p24_bus_point, _, _) = prove_gkr_quotient::<_, 2>(
            &mut prover_state,
            &MleGroupRef::ExtensionPacked(vec![&p24_bus_selector_packed, &p24_bus_data_packed]),
        );
        let p24_bus_eval_index_input_a = p24_indexes_input_a.evaluate(&p24_bus_point);
        let p24_bus_eval_index_input_b = p24_indexes_input_b.evaluate(&p24_bus_point);
        let p24_bus_eval_index_input_output = p24_indexes_output.evaluate(&p24_bus_point);
        prover_state.add_extension_scalars(&[
            p24_bus_eval_index_input_a,
            p24_bus_eval_index_input_b,
            p24_bus_eval_index_input_output,
        ]);
        (
            p24_bus_quotient,
            p24_bus_point,
            p24_bus_eval_index_input_a,
            p24_bus_eval_index_input_b,
            p24_bus_eval_index_input_output,
        )
    };

    let (mut dot_product_bus_quotient, dot_product_bus_beta, dot_product_bus_virtual_statement) = {
        let dot_product_bus_data = (0..1 << log_n_rows_dot_product_table)
            .into_par_iter()
            .map(|i| {
                bus_challenge
                    + finger_print(
                        TABLE_INDEX_DOT_PRODUCTS,
                        &[
                            dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_A][i],
                            dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_B][i],
                            dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_RES][i],
                            dot_product_columns_f[DOT_PRODUCT_AIR_COL_LEN][i],
                        ],
                        fingerprint_challenge,
                    )
            })
            .collect::<Vec<_>>();

        let dot_product_bus_selector = dot_product_columns_f[DOT_PRODUCT_AIR_COL_START_FLAG]
            .par_iter()
            .map(|&x| EF::from(-x)) // NOTE the "-" sign here !!
            .collect::<Vec<_>>(); // TODO embedding overhead !!!!!!!!!!!!!!
        let dot_product_bus_selector_packed = pack_extension(&dot_product_bus_selector);
        let dot_product_bus_data_packed = pack_extension(&dot_product_bus_data);
        let (
            dot_product_bus_quotient,
            dot_product_bus_point,
            dot_product_bus_selector_value,
            dot_product_bus_data_value,
        ) = prove_gkr_quotient::<_, TWO_POW_DOT_PRODUCT_UNIVARIATE_SKIPS>(
            &mut prover_state,
            &MleGroupRef::ExtensionPacked(vec![
                &dot_product_bus_selector_packed,
                &dot_product_bus_data_packed,
            ]),
        );

        let dot_product_bus_beta = prover_state.sample();
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
    assert_eq!(
        exec_bus_quotient
            + p16_bus_quotient
            + p24_bus_quotient
            + dot_product_bus_quotient
            + multilinear_eval_bus_quotient,
        EF::ZERO
    );

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
    let (exec_air_point, exec_evals_to_prove) = info_span!("Execution AIR proof").in_scope(|| {
        prove_air(
            &mut prover_state,
            &exec_table,
            UNIVARIATE_SKIPS,
            &full_trace.iter().map(Vec::as_slice).collect::<Vec<_>>(),
            &[],
            &execution_air_padding_row::<EF>(bytecode.ending_pc),
            Some(exec_bus_virtual_statement),
            true,
        )
    });

    let dot_product_table = AirTable::<EF, _>::new(DotProductAir {
        bus_challenge,
        fingerprint_challenge_powers: powers_const(fingerprint_challenge),
        dot_product_bus_beta,
    });

    let (dot_product_air_point, dot_product_evals_to_prove) = info_span!("DotProduct AIR proof")
        .in_scope(|| {
            prove_air(
                &mut prover_state,
                &dot_product_table,
                DOT_PRODUCT_UNIVARIATE_SKIPS,
                &dot_product_columns_f
                    .iter()
                    .map(Vec::as_slice)
                    .collect::<Vec<_>>(),
                &dot_product_columns_ef
                    .iter()
                    .map(Vec::as_slice)
                    .collect::<Vec<_>>(),
                &dot_product_air_padding_row(),
                Some(dot_product_bus_virtual_statement),
                true,
            )
        });

    let random_point_p16 = MultilinearPoint(prover_state.sample_vec(log_n_p16));
    let p16_gkr = prove_poseidon_gkr(
        &mut prover_state,
        &p16_witness,
        random_point_p16.0.clone(),
        UNIVARIATE_SKIPS,
        &p16_gkr_layers,
    );

    let random_point_p24 = MultilinearPoint(prover_state.sample_vec(log_n_p24));
    let p24_gkr = prove_poseidon_gkr(
        &mut prover_state,
        &p24_witness,
        random_point_p24.0.clone(),
        UNIVARIATE_SKIPS,
        &p24_gkr_layers,
    );

    let poseidon_value_columns = vec![
        array::from_fn(|i| FPacking::<F>::unpack_slice(&p16_witness.input_layer[i])),
        array::from_fn(|i| FPacking::<F>::unpack_slice(&p16_witness.input_layer[i + VECTOR_LEN])),
        array::from_fn(|i| {
            FPacking::<F>::unpack_slice(&p16_witness.compression.as_ref().unwrap().2[i])
        }),
        array::from_fn(|i| {
            FPacking::<F>::unpack_slice(
                &p16_witness.compression.as_ref().unwrap().2[i + VECTOR_LEN],
            )
        }),
        array::from_fn(|i| FPacking::<F>::unpack_slice(&p24_witness.input_layer[i])),
        array::from_fn(|i| FPacking::<F>::unpack_slice(&p24_witness.input_layer[i + VECTOR_LEN])),
        array::from_fn(|i| {
            FPacking::<F>::unpack_slice(&p24_witness.input_layer[i + VECTOR_LEN * 2])
        }),
        array::from_fn(|i| {
            FPacking::<F>::unpack_slice(&p24_witness.output_layer[i + VECTOR_LEN * 2])
        }),
    ];

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim_1 = Evaluation::new(
        exec_air_point.clone(),
        padd_with_zero_to_next_power_of_two(&exec_evals_to_prove[..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_poly_eq_point = eval_eq(&exec_air_point);
    let bytecode_pushforward = compute_pushforward(
        &full_trace[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    );

    let normal_lookup_into_memory = NormalPackedLookupProver::step_1(
        &mut prover_state,
        &memory,
        vec![
            &full_trace[COL_INDEX_MEM_ADDRESS_A],
            &full_trace[COL_INDEX_MEM_ADDRESS_B],
            &full_trace[COL_INDEX_MEM_ADDRESS_C],
            &dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_A],
            &dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_B],
            &dot_product_columns_f[DOT_PRODUCT_AIR_COL_INDEX_RES],
        ],
        [
            vec![n_cycles; 3],
            vec![n_rows_table_dot_products.max(1 << LOG_MIN_DOT_PRODUCT_ROWS); 3],
        ]
        .concat(),
        [vec![0; 3], vec![0; 3]].concat(),
        vec![
            &full_trace[COL_INDEX_MEM_VALUE_A],
            &full_trace[COL_INDEX_MEM_VALUE_B],
            &full_trace[COL_INDEX_MEM_VALUE_C],
        ],
        vec![
            &dot_product_columns_ef[DOT_PRODUCT_AIR_COL_VALUE_A],
            &dot_product_columns_ef[DOT_PRODUCT_AIR_COL_VALUE_B],
            &dot_product_columns_ef[DOT_PRODUCT_AIR_COL_VALUE_RES],
        ],
        normal_lookup_into_memory_initial_statements(
            &exec_air_point,
            &exec_evals_to_prove,
            &dot_product_air_point,
            &dot_product_evals_to_prove,
        ),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let vectorized_lookup_into_memory = VectorizedPackedLookupProver::<_, VECTOR_LEN>::step_1(
        &mut prover_state,
        &memory,
        vec![
            &p16_indexes_input_a,
            &p16_indexes_input_b,
            &p16_indexes_output,
            &p16_indexes_output_shifted,
            &p24_indexes_input_a,
            &p24_indexes_input_a_shifted,
            &p24_indexes_input_b,
            &p24_indexes_output,
        ],
        [
            vec![n_poseidons_16.max(1 << LOG_MIN_POSEIDONS_16); 4],
            vec![n_poseidons_24.max(1 << LOG_MIN_POSEIDONS_24); 4],
        ]
        .concat(),
        default_poseidon_indexes(),
        poseidon_value_columns,
        poseidon_lookup_statements(&p16_gkr, &p24_gkr),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    // 2nd Commitment
    let extension_pols = vec![
        normal_lookup_into_memory.pushforward_to_commit(),
        vectorized_lookup_into_memory.pushforward_to_commit(),
        bytecode_pushforward.as_slice(),
    ];

    let extension_dims = vec![
        ColDims::padded(non_zero_memory_size, EF::ZERO), // memory
        ColDims::padded(non_zero_memory_size.div_ceil(VECTOR_LEN), EF::ZERO), // memory (folded)
        ColDims::padded(bytecode.instructions.len(), EF::ZERO), // bytecode
    ];

    let packed_pcs_witness_extension = packed_pcs_commit(
        &second_batched_whir_config_builder(
            whir_config_builder.clone(),
            packed_pcs_witness_base.packed_polynomial.by_ref().n_vars(),
            num_packed_vars_for_dims::<EF>(&extension_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK),
        ),
        &extension_pols,
        &extension_dims,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let normal_lookup_into_memory_statements =
        normal_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let vectorized_lookup_statements =
        vectorized_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &full_trace[COL_INDEX_PC],
        bytecode_lookup_claim_1.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward,
        Some(bytecode.instructions.len()),
    );

    memory_statements.push(normal_lookup_into_memory_statements.on_table.clone());
    memory_statements.push(vectorized_lookup_statements.on_table.clone());

    {
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

        // prove this value via sumcheck: index_res_b = (index_res_a + 1) * (1 - compression)
        let p16_one_minus_compression = &p16_witness
            .compression
            .as_ref()
            .unwrap()
            .1
            .par_iter()
            .map(|c| EFPacking::<EF>::ONE - *c) // TODO embedding overhead
            .collect::<Vec<_>>();
        let p16_index_res_a_plus_one = pack_extension(
            &p16_indexes_output
                .par_iter()
                .map(|c| EF::ONE + *c) // TODO embedding overhead
                .collect::<Vec<_>>(),
        );
        let alpha = prover_state.sample();
        let mut poly_eq = EFPacking::<EF>::zero_vec(1 << (log_n_p16 - packing_log_width::<EF>()));
        let mut sum = EF::ZERO;
        for (statement, alpha_power) in vectorized_lookup_statements.on_indexes[3]
            .iter()
            .zip(alpha.powers())
        {
            sum += statement.value * alpha_power;
            compute_sparse_eval_eq_packed(&statement.point, &mut poly_eq, alpha_power);
        }
        // TODO there is a lot of embedding overhead in this sumcheck
        let (sc_point, sc_values, _) = sumcheck_prove(
            1,
            MleGroupRef::ExtensionPacked(vec![
                &poly_eq,
                &p16_one_minus_compression,
                &p16_index_res_a_plus_one,
            ]),
            None,
            &CubeComputation {},
            &[],
            None,
            false,
            &mut prover_state,
            sum,
            false,
        );
        prover_state.add_extension_scalar(sc_values[2]);
        p16_indexes_res_statements.push(Evaluation::new(sc_point, sc_values[2] - EF::ONE));
    }

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_computation_column_statements = dot_product_computation_ext_to_base_helper
        .after_commitment(&mut prover_state, &dot_product_air_point);

    let exec_air_statement =
        |col_index: usize| Evaluation::new(exec_air_point.clone(), exec_evals_to_prove[col_index]);
    let dot_product_air_statement = |col_index: usize| {
        Evaluation::new(
            dot_product_air_point.clone(),
            dot_product_evals_to_prove[col_index],
        )
    };

    // First Opening
    let all_base_statements = [
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
                normal_lookup_into_memory_statements.on_indexes[0].clone(),
            ]
            .concat(), // exec memory address A
            [
                vec![exec_air_statement(COL_INDEX_MEM_ADDRESS_B)],
                normal_lookup_into_memory_statements.on_indexes[1].clone(),
            ]
            .concat(), // exec memory address B
            [
                vec![exec_air_statement(COL_INDEX_MEM_ADDRESS_C)],
                normal_lookup_into_memory_statements.on_indexes[2].clone(),
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
            vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_START_FLAG)],
            vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_LEN)],
            [
                vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_A)],
                normal_lookup_into_memory_statements.on_indexes[3].clone(),
            ]
            .concat(),
            [
                vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_B)],
                normal_lookup_into_memory_statements.on_indexes[4].clone(),
            ]
            .concat(),
            [
                vec![dot_product_air_statement(DOT_PRODUCT_AIR_COL_INDEX_RES)],
                normal_lookup_into_memory_statements.on_indexes[4].clone(),
            ]
            .concat(),
        ],
        dot_product_computation_column_statements,
    ]
    .concat();

    let global_statements_base = packed_pcs_global_statements_for_prover(
        &base_pols,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &all_base_statements,
        &mut prover_state,
    );

    // Second Opening
    let global_statements_extension = packed_pcs_global_statements_for_prover(
        &extension_pols,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            normal_lookup_into_memory_statements.on_pushforward,
            vectorized_lookup_statements.on_pushforward,
            bytecode_logup_star_statements.on_pushforward,
        ],
        &mut prover_state,
    );

    WhirConfig::new(
        whir_config_builder,
        packed_pcs_witness_base.packed_polynomial.by_ref().n_vars(),
    )
    .batch_prove(
        &mut prover_state,
        global_statements_base,
        packed_pcs_witness_base.inner_witness,
        &packed_pcs_witness_base.packed_polynomial.by_ref(),
        global_statements_extension,
        packed_pcs_witness_extension.inner_witness,
        &packed_pcs_witness_extension.packed_polynomial.by_ref(),
    );

    (
        prover_state.proof_data().to_vec(),
        prover_state.proof_size(),
        exec_summary,
    )
}
