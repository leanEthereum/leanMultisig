use crate::common::*;
use crate::*;
use ::air::table::AirTable;
use lean_vm::*;
use lookup::prove_gkr_product;
use lookup::{compute_pushforward, prove_logup_star};
use multilinear_toolkit::prelude::*;
use p3_air::BaseAir;
use p3_field::Field;
use p3_field::PrimeCharacteristicRing;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use packed_pcs::*;
use std::collections::BTreeMap;
use tracing::info_span;
use utils::{
    build_poseidon_16_air, build_poseidon_24_air, build_prover_state,
    padd_with_zero_to_next_power_of_two,
};
use vm_air::*;
use whir_p3::{
    WhirConfig, WhirConfigBuilder, precompute_dft_twiddles, second_batched_whir_config_builder,
};

pub fn prove_execution(
    bytecode: &Bytecode,
    source_code: &str,                            // debug purpose
    function_locations: &BTreeMap<usize, String>, // debug purpose
    (public_input, private_input): (&[F], &[F]),
    whir_config_builder: WhirConfigBuilder,
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    vm_profiler: bool,
) -> (Vec<PF<EF>>, usize) {
    let ExecutionTrace {
        full_trace,
        n_poseidons_16,
        n_poseidons_24,
        poseidons_16, // padded with empty poseidons
        poseidons_24, // padded with empty poseidons
        dot_products,
        multilinear_evals: vm_multilinear_evals,
        public_memory_size,
        non_zero_memory_size,
        max_non_vec_memory_access,
        memory, // padded with zeros to next power of two
    } = info_span!("Witness generation").in_scope(|| {
        let execution_result = execute_bytecode(
            bytecode,
            public_input,
            private_input,
            source_code,
            function_locations,
            no_vec_runtime_memory,
            vm_profiler,
        );
        get_execution_trace(bytecode, execution_result)
    });

    let public_memory = &memory[..public_memory_size];
    let private_memory = &memory[public_memory_size..non_zero_memory_size];
    let log_memory = log2_strict_usize(memory.len());
    let log_public_memory = log2_strict_usize(public_memory.len());

    let n_cycles = full_trace[0].len();
    let log_n_cycles = log2_strict_usize(n_cycles);
    assert!(full_trace.iter().all(|col| col.len() == 1 << log_n_cycles));

    let log_n_p16 = log2_ceil_usize(n_poseidons_16);
    let log_n_p24 = log2_ceil_usize(n_poseidons_24);

    precompute_dft_twiddles::<F>(1 << 24);

    let mut exec_columns = full_trace[..N_INSTRUCTION_COLUMNS_IN_AIR]
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    exec_columns.extend(
        full_trace[N_INSTRUCTION_COLUMNS..]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
    );
    let exec_table = AirTable::<EF, _, _>::new(VMAir, VMAir);

    let _validity_proof_span = info_span!("Validity proof generation").entered();

    let p16_air = build_poseidon_16_air();
    let p24_air = build_poseidon_24_air();
    let p16_air_packed = build_poseidon_16_air_packed();
    let p24_air_packed = build_poseidon_24_air_packed();
    let p16_table = AirTable::<EF, _, _>::new(p16_air.clone(), p16_air_packed);
    let p24_table = AirTable::<EF, _, _>::new(p24_air.clone(), p24_air_packed);

    let dot_product_table = AirTable::<EF, _, _>::new(DotProductAir, DotProductAir);

    let (p16_columns, p24_columns) = build_poseidon_columns(&poseidons_16, &poseidons_24);

    let (dot_product_columns_f, dot_product_columns_ef, dot_product_padding_len) =
        build_dot_product_columns(&dot_products, &memory);

    let dot_product_index_vec_a_1 = &dot_product_columns_f
        [DOT_PRODUCT_COL_A_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1];
    let dot_product_index_vec_a_2 = &dot_product_columns_f
        [DOT_PRODUCT_COL_A_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_2];
    let dot_product_offset_a =
        &dot_product_columns_f[DOT_PRODUCT_COL_A_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET];
    let dot_product_index_vec_b_1 = &dot_product_columns_f
        [DOT_PRODUCT_COL_B_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1];
    let dot_product_index_vec_b_2 = &dot_product_columns_f
        [DOT_PRODUCT_COL_B_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_2];
    let dot_product_offset_b =
        &dot_product_columns_f[DOT_PRODUCT_COL_B_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET];
    let dot_product_index_vec_res_1 = &dot_product_columns_f
        [DOT_PRODUCT_COL_RES_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1];
    let dot_product_index_vec_res_2 = &dot_product_columns_f
        [DOT_PRODUCT_COL_RES_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_2];
    let dot_product_offset_res =
        &dot_product_columns_f[DOT_PRODUCT_COL_RES_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET];

    let dot_prouduct_value_a = &dot_product_columns_ef[DOT_PRODUCT_EF_COL_VALUE_A];
    let dot_product_value_a_base =
        transpose_slice_to_basis_coefficients::<F, EF>(dot_prouduct_value_a);

    let dot_prouduct_value_b = &dot_product_columns_ef[DOT_PRODUCT_EF_COL_VALUE_B];
    let dot_prouduct_value_b_base =
        transpose_slice_to_basis_coefficients::<F, EF>(dot_prouduct_value_b);

    let dot_prouduct_value_res = &dot_product_columns_ef[DOT_PRODUCT_EF_COL_RES];
    let dot_prouduct_value_res_base =
        transpose_slice_to_basis_coefficients::<F, EF>(dot_prouduct_value_res);

    let dot_product_computations = &dot_product_columns_ef[DOT_PRODUCT_EF_COL_COMPUTATION];
    let dot_product_computations_base =
        transpose_slice_to_basis_coefficients::<F, EF>(dot_product_computations);

    let n_rows_table_dot_products = dot_product_columns_f[0].len() - dot_product_padding_len;
    let log_n_rows_dot_product_table = log2_strict_usize(dot_product_columns_f[0].len());

    let mut prover_state = build_prover_state::<EF>();
    prover_state.add_base_scalars(
        &[
            log_n_cycles,
            n_poseidons_16,
            n_poseidons_24,
            dot_products.len(),
            n_rows_table_dot_products,
            private_memory.len(),
            max_non_vec_memory_access,
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
            &mut prover_state,
            &mut memory_statements,
        )
        .unwrap();
    }
    let p16_indexes_input = all_poseidon_16_indexes_input(&poseidons_16);
    // 0..16: input, 16: compress, 17: res_index_1, 18: res_index_2
    let p16_compression_col = &p16_columns[16];
    let p16_index_out_1_col = &p16_columns[17];

    let p24_indexes = all_poseidon_24_indexes(&poseidons_24);

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory.len(),
        bytecode.ending_pc,
        (n_poseidons_16, n_poseidons_24),
        (p16_air.width_f(), p24_air.width_f()),
        n_rows_table_dot_products,
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
        p16_indexes_input
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        p24_indexes.iter().map(Vec::as_slice).collect::<Vec<_>>(),
        p16_columns[16..p16_air.width_f() - 16]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        p24_columns[24..p24_air.width_f() - 24]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        // DOT PRODUCT COLUMNS
        vec![
            &dot_product_columns_f[DOT_PRODUCT_COL_START_FLAG],
            &dot_product_columns_f[DOT_PRODUCT_COL_LEN],
            &dot_product_columns_f[DOT_PRODUCT_COL_INDEX_A],
            &dot_product_columns_f[DOT_PRODUCT_COL_INDEX_B],
            &dot_product_columns_f[DOT_PRODUCT_COL_INDEX_RES],
        ],
        dot_product_value_a_base
            .iter()
            .map(Vec::as_slice)
            .collect(),
        dot_prouduct_value_b_base
            .iter()
            .map(Vec::as_slice)
            .collect(),
        dot_prouduct_value_res_base
            .iter()
            .map(Vec::as_slice)
            .collect(),
        dot_product_computations_base
            .iter()
            .map(Vec::as_slice)
            .collect(),
        vec![
            dot_product_index_vec_a_1.as_slice(),
            dot_product_offset_a.as_slice(),
            dot_product_index_vec_b_1.as_slice(),
            dot_product_offset_b.as_slice(),
            dot_product_index_vec_res_1.as_slice(),
            dot_product_offset_res.as_slice(),
        ],
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

    // Grand Product for consistency with precompiles
    let grand_product_challenge_global = prover_state.sample();
    let grand_product_challenge_p16 = prover_state.sample();
    let grand_product_challenge_p24 = prover_state.sample();
    let grand_product_challenge_dot_product = prover_state.sample();
    let grand_product_challenge_vm_multilinear_eval = prover_state.sample();
    let mut exec_column_for_grand_product = vec![grand_product_challenge_global; n_cycles];
    for pos_16 in &poseidons_16 {
        let Some(cycle) = pos_16.cycle else {
            break;
        };
        exec_column_for_grand_product[cycle] = grand_product_challenge_global
            + finger_print(&pos_16.addresses_field_repr(), grand_product_challenge_p16);
    }
    for pos_24 in &poseidons_24 {
        let Some(cycle) = pos_24.cycle else {
            break;
        };
        exec_column_for_grand_product[cycle] = grand_product_challenge_global
            + finger_print(&pos_24.addresses_field_repr(), grand_product_challenge_p24);
    }
    for dot_product in &dot_products {
        exec_column_for_grand_product[dot_product.cycle] = grand_product_challenge_global
            + finger_print(
                &dot_product.addresses_and_len_field_repr(),
                grand_product_challenge_dot_product,
            );
    }
    for multilinear_eval in &vm_multilinear_evals {
        exec_column_for_grand_product[multilinear_eval.cycle] = grand_product_challenge_global
            + finger_print(
                &multilinear_eval.addresses_and_n_vars_field_repr(),
                grand_product_challenge_vm_multilinear_eval,
            );
    }

    let (grand_product_exec_res, grand_product_exec_statement) = prove_gkr_product(
        &mut prover_state,
        pack_extension(&exec_column_for_grand_product),
    );

    let p16_column_for_grand_product = poseidons_16
        .par_iter()
        .map(|pos_16| {
            grand_product_challenge_global
                + finger_print(&pos_16.addresses_field_repr(), grand_product_challenge_p16)
        })
        .collect::<Vec<_>>();

    let (grand_product_p16_res, grand_product_p16_statement) = prove_gkr_product(
        &mut prover_state,
        pack_extension(&p16_column_for_grand_product),
    );

    let p24_column_for_grand_product = poseidons_24
        .par_iter()
        .map(|pos_24| {
            grand_product_challenge_global
                + finger_print(&pos_24.addresses_field_repr(), grand_product_challenge_p24)
        })
        .collect::<Vec<_>>();

    let (grand_product_p24_res, grand_product_p24_statement) = prove_gkr_product(
        &mut prover_state,
        pack_extension(&p24_column_for_grand_product),
    );

    let dot_product_column_for_grand_product = (0..1 << log_n_rows_dot_product_table)
        .into_par_iter()
        .map(|i| {
            grand_product_challenge_global
                + if dot_product_columns_f[DOT_PRODUCT_COL_START_FLAG][i].is_zero() {
                    grand_product_challenge_dot_product
                } else {
                    finger_print(
                        &[
                            dot_product_columns_f[DOT_PRODUCT_COL_INDEX_A][i],
                            dot_product_columns_f[DOT_PRODUCT_COL_INDEX_B][i],
                            dot_product_columns_f[DOT_PRODUCT_COL_INDEX_RES][i],
                            dot_product_columns_f[DOT_PRODUCT_COL_LEN][i],
                        ],
                        grand_product_challenge_dot_product,
                    )
                }
        })
        .collect::<Vec<_>>();

    let vm_multilinear_eval_grand_product_res = vm_multilinear_evals
        .par_iter()
        .map(|vm_multilinear_eval| {
            grand_product_challenge_global
                + finger_print(
                    &vm_multilinear_eval.addresses_and_n_vars_field_repr(),
                    grand_product_challenge_vm_multilinear_eval,
                )
        })
        .product::<EF>();

    let (grand_product_dot_product_res, grand_product_dot_product_statement) = prove_gkr_product(
        &mut prover_state,
        pack_extension(&dot_product_column_for_grand_product),
    );

    let corrected_prod_exec = grand_product_exec_res
        / grand_product_challenge_global.exp_u64(
            (n_cycles
                - n_poseidons_16
                - n_poseidons_24
                - dot_products.len()
                - vm_multilinear_evals.len()) as u64,
        );
    let corrected_prod_p16 = grand_product_p16_res
        / (grand_product_challenge_global
            + grand_product_challenge_p16
            + grand_product_challenge_p16.exp_u64(4) * F::from_usize(POSEIDON_16_NULL_HASH_PTR)
            + grand_product_challenge_p16.exp_u64(5) * F::ONE) // compression = 1 by default
            .exp_u64((n_poseidons_16.next_power_of_two() - n_poseidons_16) as u64);

    let corrected_prod_p24 = grand_product_p24_res
        / (grand_product_challenge_global
            + grand_product_challenge_p24
            + grand_product_challenge_p24.exp_u64(4) * F::from_usize(POSEIDON_24_NULL_HASH_PTR))
        .exp_u64((n_poseidons_24.next_power_of_two() - n_poseidons_24) as u64);

    let corrected_dot_product = grand_product_dot_product_res
        / ((grand_product_challenge_global
            + grand_product_challenge_dot_product
            + grand_product_challenge_dot_product.exp_u64(5))
        .exp_u64(dot_product_padding_len as u64)
            * (grand_product_challenge_global + grand_product_challenge_dot_product).exp_u64(
                ((1 << log_n_rows_dot_product_table) - dot_product_padding_len - dot_products.len())
                    as u64,
            ));

    assert_eq!(
        corrected_prod_exec,
        corrected_prod_p16
            * corrected_prod_p24
            * corrected_dot_product
            * vm_multilinear_eval_grand_product_res
    );

    let p16_grand_product_evals_on_indexes_a =
        p16_indexes_input[0].evaluate(&grand_product_p16_statement.point);
    let p16_grand_product_evals_on_indexes_b =
        p16_indexes_input[1].evaluate(&grand_product_p16_statement.point);
    let p16_grand_product_evals_on_indexes_res =
        p16_index_out_1_col.evaluate(&grand_product_p16_statement.point);
    let p16_grand_product_evals_on_compression =
        p16_compression_col.evaluate(&grand_product_p16_statement.point);
    prover_state.add_extension_scalars(&[
        p16_grand_product_evals_on_indexes_a,
        p16_grand_product_evals_on_indexes_b,
        p16_grand_product_evals_on_indexes_res,
        p16_grand_product_evals_on_compression,
    ]);

    let mut p16_indexes_a_statements = vec![Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_a,
    )];
    let mut p16_indexes_b_statements = vec![Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_b,
    )];

    let p24_grand_product_evals_on_indexes_a =
        p24_indexes[0].evaluate(&grand_product_p24_statement.point);
    let p24_grand_product_evals_on_indexes_b =
        p24_indexes[1].evaluate(&grand_product_p24_statement.point);
    let p24_grand_product_evals_on_indexes_res =
        p24_indexes[2].evaluate(&grand_product_p24_statement.point);
    prover_state.add_extension_scalars(&[
        p24_grand_product_evals_on_indexes_a,
        p24_grand_product_evals_on_indexes_b,
        p24_grand_product_evals_on_indexes_res,
    ]);

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

    let dot_product_footprint_computation = DotProductFootprint {
        global_challenge: grand_product_challenge_global,
        dot_product_challenge: powers_const(grand_product_challenge_dot_product),
    };

    let (
        grand_product_dot_product_sumcheck_point,
        grand_product_dot_product_sumcheck_inner_evals,
        _,
    ) = info_span!("Grand product sumcheck for Dot Product").in_scope(|| {
        sumcheck_prove(
            1,
            MleGroupRef::Base(
                dot_product_columns_f[..5]
                    .iter()
                    .map(|c| c.as_slice())
                    .collect::<Vec<_>>(),
            )
            .pack(),
            None,
            &dot_product_footprint_computation,
            &dot_product_footprint_computation,
            &[],
            Some((grand_product_dot_product_statement.point.0.clone(), None)),
            false,
            &mut prover_state,
            grand_product_dot_product_statement.value,
            None,
        )
    });
    assert_eq!(grand_product_dot_product_sumcheck_inner_evals.len(), 5);
    prover_state.add_extension_scalars(&grand_product_dot_product_sumcheck_inner_evals);

    let grand_product_dot_product_flag_statement = Evaluation::new(
        grand_product_dot_product_sumcheck_point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[0],
    );

    let grand_product_dot_product_len_statement = Evaluation::new(
        grand_product_dot_product_sumcheck_point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[1],
    );

    let grand_product_dot_product_table_indexes_statement_index_a = Evaluation::new(
        grand_product_dot_product_sumcheck_point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[2],
    );
    let grand_product_dot_product_table_indexes_statement_index_b = Evaluation::new(
        grand_product_dot_product_sumcheck_point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[3],
    );
    let grand_product_dot_product_table_indexes_statement_index_res = Evaluation::new(
        grand_product_dot_product_sumcheck_point.clone(),
        grand_product_dot_product_sumcheck_inner_evals[4],
    );

    let precompile_foot_print_computation = PrecompileFootprint {
        global_challenge: grand_product_challenge_global,
        p16_powers: powers_const(grand_product_challenge_p16),
        p24_powers: powers_const(grand_product_challenge_p24),
        dot_product_powers: powers_const(grand_product_challenge_dot_product),
        multilinear_eval_powers: powers_const(grand_product_challenge_vm_multilinear_eval),
    };

    let (grand_product_exec_sumcheck_point, mut grand_product_exec_sumcheck_inner_evals, _) =
        info_span!("Grand product sumcheck for Execution").in_scope(|| {
            sumcheck_prove(
                1, // TODO univariate skip
                MleGroupRef::Base(
                    reorder_full_trace_for_precomp_foot_print(
                        full_trace.iter().collect::<Vec<_>>(),
                    )
                    .iter()
                    .map(|c| c.as_slice())
                    .collect::<Vec<_>>(),
                )
                .pack(),
                None,
                &precompile_foot_print_computation,
                &precompile_foot_print_computation,
                &[],
                Some((grand_product_exec_statement.point.0.clone(), None)),
                false,
                &mut prover_state,
                grand_product_exec_statement.value,
                None,
            )
        });

    // TODO compute eq polynomial 1 time and then inner product with each column
    for col in [
        COL_INDEX_OPERAND_C,
        COL_INDEX_ADD,
        COL_INDEX_MUL,
        COL_INDEX_DEREF,
        COL_INDEX_JUMP,
        COL_INDEX_PC,
        COL_INDEX_MEM_ADDRESS_A,
        COL_INDEX_MEM_ADDRESS_B,
        COL_INDEX_MEM_ADDRESS_C,
    ] {
        grand_product_exec_sumcheck_inner_evals.insert(
            col,
            full_trace[col].evaluate(&grand_product_exec_sumcheck_point),
        );
    }
    assert_eq!(
        N_TOTAL_COLUMNS,
        grand_product_exec_sumcheck_inner_evals.len()
    );
    prover_state.add_extension_scalars(&grand_product_exec_sumcheck_inner_evals);

    let grand_product_exec_evals_on_each_column =
        &grand_product_exec_sumcheck_inner_evals[..N_INSTRUCTION_COLUMNS];

    let grand_product_fp_statement = Evaluation::new(
        grand_product_exec_sumcheck_point.clone(),
        grand_product_exec_sumcheck_inner_evals[COL_INDEX_FP],
    );

    let (exec_air_point, exec_evals_to_prove) = info_span!("Execution AIR proof")
        .in_scope(|| exec_table.prove(&mut prover_state, UNIVARIATE_SKIPS, &exec_columns));

    let dot_product_columns_f_ref = dot_product_columns_f
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let dot_product_columns_ef_ref = dot_product_columns_ef
        .iter()
        .map(Vec::as_slice)
        .collect::<Vec<_>>();
    let (dot_product_air_point, dot_product_evals_to_prove) = info_span!("DotProduct AIR proof")
        .in_scope(|| {
            dot_product_table.prove_2(
                &mut prover_state,
                UNIVARIATE_SKIPS,
                &dot_product_columns_f_ref,
                &dot_product_columns_ef_ref,
            )
        });

    let mut dot_product_vec_index_a_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_A_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1],
    )];
    let mut dot_product_vec_index_b_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_B_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1],
    )];
    let mut dot_product_vec_index_res_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_RES_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_INDEX_VEC_1],
    )];
    let dot_product_offset_a_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_A_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET],
    )];
    let dot_product_offset_b_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_B_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET],
    )];
    let dot_product_offset_res_statements = vec![Evaluation::new(
        dot_product_air_point.clone(),
        dot_product_evals_to_prove[DOT_PRODUCT_COL_RES_JUSTIFICATION_START + DOT_PRODUCT_SUBCOL_OFFSET],
    )];

    let p16_columns_ref = p16_columns.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let (p16_air_point, p16_evals_to_prove) = info_span!("Poseidon-16 AIR proof")
        .in_scope(|| p16_table.prove(&mut prover_state, UNIVARIATE_SKIPS, &p16_columns_ref));
    let mut p16_statements = p16_evals_to_prove[16..p16_air.width_f() - 16]
        .iter()
        .map(|&e| vec![Evaluation::new(p16_air_point.clone(), e)])
        .collect::<Vec<_>>();
    p16_statements[0].push(Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_compression,
    ));

    p16_statements[1].push(Evaluation::new(
        grand_product_p16_statement.point.clone(),
        p16_grand_product_evals_on_indexes_res,
    ));

    let p24_columns_ref = p24_columns.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let (p24_air_point, p24_evals_to_prove) = info_span!("Poseidon-24 AIR proof")
        .in_scope(|| p24_table.prove(&mut prover_state, UNIVARIATE_SKIPS, &p24_columns_ref));
    let p24_statements = p24_evals_to_prove[24..p24_air.width_f() - 24]
        .iter()
        .map(|&e| vec![Evaluation::new(p24_air_point.clone(), e)])
        .collect();

    // Poseidons 16/24 memory addresses lookup
    let precompile_logup_star_alpha = prover_state.sample();
    let memory_folding_challenges = MultilinearPoint(prover_state.sample_vec(LOG_VECTOR_LEN));

    let poseidon_lookup_statements = get_poseidon_lookup_statements(
        (p16_air.width_f(), p24_air.width_f()),
        (log_n_p16, log_n_p24),
        (&p16_evals_to_prove, &p24_evals_to_prove),
        (&p16_air_point, &p24_air_point),
        &memory_folding_challenges,
    );

    let all_poseidon_indexes = full_poseidon_indexes(&poseidons_16, &poseidons_24);

    let precompile_folded_memory = fold_multilinear_chunks(&memory, &memory_folding_challenges);

    let mut poseidon_poly_eq_point = EF::zero_vec(all_poseidon_indexes.len());
    for (i, statement) in poseidon_lookup_statements.iter().enumerate() {
        compute_sparse_eval_eq::<EF>(
            &statement.point,
            &mut poseidon_poly_eq_point,
            precompile_logup_star_alpha.exp_u64(i as u64),
        );
    }

    let poseidon_pushforward = compute_pushforward(
        &all_poseidon_indexes,
        precompile_folded_memory.len(),
        &poseidon_poly_eq_point,
    );

    // Dot product memory addresses lookup

    let dot_product_lookup_statements = get_dot_product_lookup_statements(
        &dot_product_evals_to_prove,
        &dot_product_air_point,
        &memory_folding_challenges,
    );

    let all_dot_product_vec_indexes = [
        dot_product_index_vec_a_1.clone(),
        dot_product_index_vec_a_2.clone(),
        dot_product_index_vec_b_1.clone(),
        dot_product_index_vec_b_2.clone(),
        dot_product_index_vec_res_1.clone(),
        dot_product_index_vec_res_2.clone(),
        F::zero_vec(dot_product_index_vec_a_1.len() * 2), // padding
    ]
    .concat();

    let mut dot_product_poly_eq_point = EF::zero_vec(all_dot_product_vec_indexes.len());
    for (i, statement) in dot_product_lookup_statements.iter().enumerate() {
        compute_sparse_eval_eq::<EF>(
            &statement.point,
            &mut dot_product_poly_eq_point,
            precompile_logup_star_alpha.exp_u64(i as u64),
        );
    }

    let dot_product_pushforward = compute_pushforward(
        &all_dot_product_vec_indexes,
        precompile_folded_memory.len(),
        &dot_product_poly_eq_point,
    );

    let non_used_precompiles_evals = full_trace
        [N_INSTRUCTION_COLUMNS_IN_AIR..N_INSTRUCTION_COLUMNS]
        .iter()
        .map(|col| col.evaluate(&exec_air_point))
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&non_used_precompiles_evals);
    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim_1 = Evaluation::new(
        exec_air_point.clone(),
        padd_with_zero_to_next_power_of_two(
            &[
                (0..N_INSTRUCTION_COLUMNS_IN_AIR)
                    .map(|i| exec_evals_to_prove[i])
                    .collect::<Vec<_>>(),
                non_used_precompiles_evals,
            ]
            .concat(),
        )
        .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_lookup_point_2 = grand_product_exec_sumcheck_point.clone();
    let bytecode_lookup_claim_2 = Evaluation::new(
        bytecode_lookup_point_2.clone(),
        padd_with_zero_to_next_power_of_two(grand_product_exec_evals_on_each_column)
            .evaluate(&bytecode_compression_challenges),
    );
    let alpha_bytecode_lookup = prover_state.sample();

    let mut bytecode_poly_eq_point = eval_eq(&exec_air_point);
    compute_eval_eq::<PF<EF>, EF, true>(
        &bytecode_lookup_point_2,
        &mut bytecode_poly_eq_point,
        alpha_bytecode_lookup,
    );
    let bytecode_pushforward = compute_pushforward(
        &full_trace[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    );

    let grand_product_mem_values_mixing_challenges = MultilinearPoint(prover_state.sample_vec(2));
    let base_memory_lookup_statement_1 = Evaluation::new(
        [
            grand_product_mem_values_mixing_challenges.0.clone(),
            grand_product_exec_sumcheck_point.0,
        ]
        .concat(),
        [
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_A],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_B],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_C],
            EF::ZERO,
        ]
        .evaluate(&grand_product_mem_values_mixing_challenges),
    );

    let exec_air_mem_values_mixing_challenges = MultilinearPoint(prover_state.sample_vec(2));
    let base_memory_lookup_statement_2 = Evaluation::new(
        [
            exec_air_mem_values_mixing_challenges.0.clone(),
            exec_air_point.0.clone(),
        ]
        .concat(),
        [
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_A.index_in_air()],
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_B.index_in_air()],
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_C.index_in_air()],
            EF::ZERO,
        ]
        .evaluate(&exec_air_mem_values_mixing_challenges),
    );

    // Main memory lookup
    let base_memory_indexes = [
        full_trace[COL_INDEX_MEM_ADDRESS_A].clone(),
        full_trace[COL_INDEX_MEM_ADDRESS_B].clone(),
        full_trace[COL_INDEX_MEM_ADDRESS_C].clone(),
        F::zero_vec(n_cycles),
    ]
    .concat();

    let memory_poly_eq_point_alpha = prover_state.sample();

    let mut base_memory_poly_eq_point = eval_eq(&base_memory_lookup_statement_1.point);
    compute_eval_eq::<PF<EF>, EF, true>(
        &base_memory_lookup_statement_2.point,
        &mut base_memory_poly_eq_point,
        memory_poly_eq_point_alpha,
    );
    let base_memory_pushforward = compute_pushforward(
        &base_memory_indexes,
        memory.len(),
        &base_memory_poly_eq_point,
    );

    // 2nd Commitment
    let extension_pols = vec![
        base_memory_pushforward.as_slice(),
        poseidon_pushforward.as_slice(),
        dot_product_pushforward.as_slice(),
        bytecode_pushforward.as_slice(),
    ];

    let extension_dims = get_extension_dims(
        non_zero_memory_size,
        max_non_vec_memory_access,
        bytecode.instructions.len(),
    );

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

    let base_memory_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Base(&memory),
        &base_memory_indexes,
        base_memory_lookup_statement_1.value
            + memory_poly_eq_point_alpha * base_memory_lookup_statement_2.value,
        &base_memory_poly_eq_point,
        &base_memory_pushforward,
        Some(non_zero_memory_size),
    );
    let poseidon_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&precompile_folded_memory),
        &all_poseidon_indexes,
        poseidon_lookup_statements
            .iter()
            .enumerate()
            .map(|(i, s)| s.value * precompile_logup_star_alpha.exp_u64(i as u64))
            .sum(),
        &poseidon_poly_eq_point,
        &poseidon_pushforward,
        Some(non_zero_memory_size.div_ceil(VECTOR_LEN)),
    );

    let dot_product_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&precompile_folded_memory),
        &all_dot_product_vec_indexes,
        dot_product_lookup_statements
            .iter()
            .enumerate()
            .map(|(i, s)| s.value * precompile_logup_star_alpha.exp_u64(i as u64))
            .sum(),
        &dot_product_poly_eq_point,
        &dot_product_pushforward,
        Some(non_zero_memory_size.div_ceil(VECTOR_LEN)),
    );

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &full_trace[COL_INDEX_PC],
        bytecode_lookup_claim_1.value + alpha_bytecode_lookup * bytecode_lookup_claim_2.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward,
        Some(bytecode.instructions.len()),
    );

    let poseidon_lookup_memory_point = MultilinearPoint(
        [
            poseidon_logup_star_statements.on_table.point.0.clone(),
            memory_folding_challenges.0.clone(),
        ]
        .concat(),
    );
    let dot_product_lookup_memory_point = MultilinearPoint(
        [
            dot_product_logup_star_statements.on_table.point.0.clone(),
            memory_folding_challenges.0.clone(),
        ]
        .concat(),
    );

    memory_statements.push(base_memory_logup_star_statements.on_table.clone());
    memory_statements.push(Evaluation::new(
        poseidon_lookup_memory_point.clone(),
        poseidon_logup_star_statements.on_table.value,
    ));
    memory_statements.push(Evaluation::new(
        dot_product_lookup_memory_point.clone(),
        dot_product_logup_star_statements.on_table.value,
    ));

    {
        // index opening for poseidon lookup

        let (correcting_factor_p16, correcting_factor_p24) = poseidon_lookup_correcting_factors(
            log_n_p16,
            log_n_p24,
            &poseidon_logup_star_statements.on_indexes.point,
        );
        let poseidon_index_evals = fold_multilinear_chunks(
            &all_poseidon_indexes,
            &MultilinearPoint(poseidon_logup_star_statements.on_indexes.point[3..].to_vec()),
        );
        let inner_values = [
            poseidon_index_evals[0] / correcting_factor_p16,
            poseidon_index_evals[1] / correcting_factor_p16,
            poseidon_index_evals[2] / correcting_factor_p16,
            poseidon_index_evals[3] / correcting_factor_p16,
            poseidon_index_evals[4] / correcting_factor_p24,
            // skip 5
            poseidon_index_evals[6] / correcting_factor_p24,
            poseidon_index_evals[7] / correcting_factor_p24,
        ];

        prover_state.add_extension_scalars(&inner_values);

        let (left, right) = p16_statements.split_at_mut(2);
        let p16_statements_res_1 = &mut left[1];
        let p16_statements_res_2 = &mut right[0];

        add_poseidon_lookup_statements_on_indexes(
            log_n_p16,
            log_n_p24,
            &poseidon_logup_star_statements.on_indexes.point,
            &inner_values,
            [
                &mut p16_indexes_a_statements,
                &mut p16_indexes_b_statements,
                p16_statements_res_1,
                p16_statements_res_2,
            ],
            [
                &mut p24_indexes_a_statements,
                &mut p24_indexes_b_statements,
                &mut p24_indexes_res_statements,
            ],
        );
    }

    {
        // index opening for dot product lookup

        let folded_dot_product_vec_index_point =
            MultilinearPoint(dot_product_logup_star_statements.on_indexes.point[3..].to_vec());

        let dot_product_vec_index_evals = fold_multilinear_chunks(
            &all_dot_product_vec_indexes,
            &folded_dot_product_vec_index_point,
        );
        assert_eq!(
            dot_product_vec_index_evals[1],
            dot_product_vec_index_evals[0] + F::ONE
        );
        assert_eq!(
            dot_product_vec_index_evals[3],
            dot_product_vec_index_evals[2] + F::ONE
        );
        assert_eq!(
            dot_product_vec_index_evals[5],
            dot_product_vec_index_evals[4] + F::ONE
        );
        assert_eq!(dot_product_vec_index_evals[6], EF::ZERO);
        assert_eq!(dot_product_vec_index_evals[7], EF::ZERO);

        assert_eq!(
            dot_product_vec_index_evals.evaluate(&MultilinearPoint(
                dot_product_logup_star_statements.on_indexes.point[..3].to_vec()
            )),
            dot_product_logup_star_statements.on_indexes.value
        );

        prover_state.add_extension_scalars(&[
            dot_product_vec_index_evals[0],
            dot_product_vec_index_evals[2],
            dot_product_vec_index_evals[4],
        ]);

        dot_product_vec_index_a_statements.push(Evaluation::new(
            folded_dot_product_vec_index_point.clone(),
            dot_product_vec_index_evals[0],
        ));
        dot_product_vec_index_b_statements.push(Evaluation::new(
            folded_dot_product_vec_index_point.clone(),
            dot_product_vec_index_evals[2],
        ));
        dot_product_vec_index_res_statements.push(Evaluation::new(
            folded_dot_product_vec_index_point.clone(),
            dot_product_vec_index_evals[4],
        ));
    }

    let (initial_pc_statement, final_pc_statement) =
        intitial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_value_a_column_evals = dot_product_value_a_base
        .par_iter()
        .map(|slice| slice.evaluate(&dot_product_air_point))
        .collect::<Vec<_>>();
    let dot_product_value_b_column_evals = dot_prouduct_value_b_base
        .par_iter()
        .map(|slice| slice.evaluate(&dot_product_air_point))
        .collect::<Vec<_>>();
    let dot_product_value_res_column_evals = dot_prouduct_value_res_base
        .par_iter()
        .map(|slice| slice.evaluate(&dot_product_air_point))
        .collect::<Vec<_>>();
    let dot_product_computation_column_evals = dot_product_computations_base
        .par_iter()
        .map(|slice| slice.evaluate(&dot_product_air_point))
        .collect::<Vec<_>>();

    prover_state.add_extension_scalars(&dot_product_value_a_column_evals);
    prover_state.add_extension_scalars(&dot_product_value_b_column_evals);
    prover_state.add_extension_scalars(&dot_product_value_res_column_evals);
    prover_state.add_extension_scalars(&dot_product_computation_column_evals);
    let dot_product_value_a_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_value_a_column_evals[i],
            )]
        })
        .collect::<Vec<_>>();
    let dot_product_value_b_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_value_b_column_evals[i],
            )]
        })
        .collect::<Vec<_>>();
    let dot_product_value_res_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_value_res_column_evals[i],
            )]
        })
        .collect::<Vec<_>>();
    let dot_product_computation_column_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation::new(
                dot_product_air_point.clone(),
                dot_product_computation_column_evals[i],
            )]
        })
        .collect::<Vec<_>>();

    let mem_lookup_eval_indexes_partial_point =
        MultilinearPoint(base_memory_logup_star_statements.on_indexes.point[2..].to_vec());
    let mem_lookup_eval_indexes_a =
        full_trace[COL_INDEX_MEM_ADDRESS_A].evaluate(&mem_lookup_eval_indexes_partial_point); // validity is proven via PCS
    let mem_lookup_eval_indexes_b =
        full_trace[COL_INDEX_MEM_ADDRESS_B].evaluate(&mem_lookup_eval_indexes_partial_point); // validity is proven via PCS
    let mem_lookup_eval_indexes_c =
        full_trace[COL_INDEX_MEM_ADDRESS_C].evaluate(&mem_lookup_eval_indexes_partial_point); // validity is proven via PCS
    assert_eq!(mem_lookup_eval_indexes_partial_point.len(), log_n_cycles);

    prover_state.add_extension_scalars(&[
        mem_lookup_eval_indexes_a,
        mem_lookup_eval_indexes_b,
        mem_lookup_eval_indexes_c,
    ]);

    let exec_air_statement = |col_index: usize| {
        Evaluation::new(
            exec_air_point.clone(),
            exec_evals_to_prove[col_index.index_in_air()],
        )
    };
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
            vec![exec_air_statement(COL_INDEX_FP), grand_product_fp_statement], // fp
            vec![
                exec_air_statement(COL_INDEX_MEM_ADDRESS_A),
                Evaluation::new(
                    mem_lookup_eval_indexes_partial_point.clone(),
                    mem_lookup_eval_indexes_a,
                ),
            ], // exec memory address A
            vec![
                exec_air_statement(COL_INDEX_MEM_ADDRESS_B),
                Evaluation::new(
                    mem_lookup_eval_indexes_partial_point.clone(),
                    mem_lookup_eval_indexes_b,
                ),
            ], // exec memory address B
            vec![
                exec_air_statement(COL_INDEX_MEM_ADDRESS_C),
                Evaluation::new(
                    mem_lookup_eval_indexes_partial_point,
                    mem_lookup_eval_indexes_c,
                ),
            ], // exec memory address C
            p16_indexes_a_statements,
            p16_indexes_b_statements,
            p24_indexes_a_statements,
            p24_indexes_b_statements,
            p24_indexes_res_statements,
        ],
        p16_statements,
        p24_statements,
        vec![
            vec![
                dot_product_air_statement(DOT_PRODUCT_COL_START_FLAG),
                grand_product_dot_product_flag_statement,
            ], // dot product: (start) flag
            vec![
                dot_product_air_statement(DOT_PRODUCT_COL_LEN),
                grand_product_dot_product_len_statement,
            ], // dot product: length
            vec![
                dot_product_air_statement(DOT_PRODUCT_COL_INDEX_A),
                grand_product_dot_product_table_indexes_statement_index_a,
            ], // dot product: indexe a
            vec![
                dot_product_air_statement(DOT_PRODUCT_COL_INDEX_B),
                grand_product_dot_product_table_indexes_statement_index_b,
            ], // dot product: indexe b
            vec![
                dot_product_air_statement(DOT_PRODUCT_COL_INDEX_RES),
                grand_product_dot_product_table_indexes_statement_index_res,
            ], // dot product: indexe res
        ],
        dot_product_value_a_statements,
        dot_product_value_b_statements,
        dot_product_value_res_statements,
        dot_product_computation_column_statements,
        vec![
            dot_product_vec_index_a_statements,
            dot_product_offset_a_statements,
            dot_product_vec_index_b_statements,
            dot_product_offset_b_statements,
            dot_product_vec_index_res_statements,
            dot_product_offset_res_statements,
        ],
    ]
    .concat();
    let global_statements_base = packed_pcs_global_statements_for_prover(
        &base_pols,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &all_base_statements,
        &mut prover_state,
    );

    let global_statements_extension = [
        base_memory_logup_star_statements.on_pushforward,
        poseidon_logup_star_statements.on_pushforward,
        dot_product_logup_star_statements.on_pushforward,
        bytecode_logup_star_statements.on_pushforward,
    ];

    // Second Opening
    let global_statements_extension = packed_pcs_global_statements_for_prover(
        &extension_pols,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &global_statements_extension,
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

    tracing::info!(
        "max_non_vec_memory_access = {} ({:.1}% of memory)",
        max_non_vec_memory_access,
        max_non_vec_memory_access as f64 * 100. / non_zero_memory_size as f64
    );

    (
        prover_state.proof_data().to_vec(),
        prover_state.proof_size(),
    )
}
