use crate::common::*;
use crate::*;
use ::air::{table::AirTable, witness::AirWitness};
use lean_vm::*;
use lookup::prove_gkr_product;
use lookup::{compute_pushforward, prove_logup_star};
use p3_air::BaseAir;
use p3_field::BasedVectorSpace;
use p3_field::ExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use pcs::{BatchPCS, packed_pcs_commit, packed_pcs_global_statements_for_prover};
use pcs::{ColDims, num_packed_vars_for_dims};
use rayon::prelude::*;
use std::collections::BTreeMap;
use sumcheck::MleGroupRef;
use tracing::info_span;
use utils::ToUsize;
use utils::assert_eq_many;
use utils::dot_product_with_base;
use utils::field_slice_as_base;
use utils::pack_extension;
use utils::{
    Evaluation, PF, build_poseidon_16_air, build_poseidon_24_air, build_prover_state,
    padd_with_zero_to_next_power_of_two,
};
use vm_air::*;
use whir_p3::dft::EvalsDft;
use whir_p3::poly::evals::{eval_eq, fold_multilinear};
use whir_p3::poly::{evals::EvaluationsList, multilinear::MultilinearPoint};
use whir_p3::utils::{compute_eval_eq, compute_sparse_eval_eq};

pub fn prove_execution(
    bytecode: &Bytecode,
    source_code: &str,                            // debug purpose
    function_locations: &BTreeMap<usize, String>, // debug purpose
    public_input: &[F],
    private_input: &[F],
    pcs: &impl BatchPCS<PF<EF>, EF, EF>,
    vm_profiler: bool,
) -> (Vec<PF<EF>>, usize) {
    let ExecutionTrace {
        full_trace,
        n_poseidons_16,
        n_poseidons_24,
        poseidons_16, // padded with empty poseidons
        poseidons_24, // padded with empty poseidons
        dot_products,
        vm_multilinear_evals,
        public_memory_size,
        memory,
    } = info_span!("Witness generation").in_scope(|| {
        let execution_result = execute_bytecode(
            bytecode,
            public_input,
            private_input,
            source_code,
            function_locations,
            vm_profiler,
        );
        get_execution_trace(bytecode, &execution_result)
    });

    let public_memory = &memory[..public_memory_size];
    let private_memory = &memory[public_memory_size..];
    let log_memory = log2_ceil_usize(memory.len());
    let log_public_memory = log2_strict_usize(public_memory.len());
    let padded_memory = padd_with_zero_to_next_power_of_two(&memory); // TODO avoid this padding

    let n_cycles = full_trace[0].len();
    let log_n_cycles = log2_strict_usize(n_cycles);
    assert!(full_trace.iter().all(|col| col.len() == 1 << log_n_cycles));

    let dft = EvalsDft::default();

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
    let exec_witness = AirWitness::<PF<EF>>::new(&exec_columns, &exec_column_groups());
    let exec_table = AirTable::<EF, _, _>::new(VMAir, VMAir);

    // exec_table.check_trace_validity(&exec_witness).unwrap();

    let _validity_proof_span = info_span!("Validity proof generation").entered();

    let p16_air = build_poseidon_16_air();
    let p24_air = build_poseidon_24_air();
    let p16_air_packed = build_poseidon_16_air_packed();
    let p24_air_packed = build_poseidon_24_air_packed();
    let p16_table = AirTable::<EF, _, _>::new(p16_air.clone(), p16_air_packed);
    let p24_table = AirTable::<EF, _, _>::new(p24_air.clone(), p24_air_packed);

    let dot_product_table = AirTable::<EF, _, _>::new(DotProductAir, DotProductAir);

    let (p16_columns, p24_columns) = build_poseidon_columns(&poseidons_16, &poseidons_24);
    let p16_witness = AirWitness::new(&p16_columns, &poseidon_16_column_groups(&p16_air));
    let p24_witness = AirWitness::new(&p24_columns, &poseidon_24_column_groups(&p24_air));

    let (dot_product_columns, dot_product_padding_len) = build_dot_product_columns(&dot_products);
    let dot_product_witness = AirWitness::new(&dot_product_columns, &DOT_PRODUCT_AIR_COLUMN_GROUPS);

    let dot_product_flags: Vec<PF<EF>> = field_slice_as_base(&dot_product_columns[0]).unwrap();
    let dot_product_lengths: Vec<PF<EF>> = field_slice_as_base(&dot_product_columns[1]).unwrap();

    let dot_product_computations: &[EF] = &dot_product_columns[8];
    let mut dot_product_computations_base = (0..DIMENSION).map(|_| Vec::new()).collect::<Vec<_>>();
    for row in dot_product_computations {
        for (j, coeff) in <EF as BasedVectorSpace<PF<EF>>>::as_basis_coefficients_slice(row)
            .iter()
            .enumerate()
        {
            dot_product_computations_base[j].push(*coeff);
        }
    }

    let n_rows_table_dot_products = dot_product_columns[0].len() - dot_product_padding_len;
    let log_n_rows_dot_product_table = log2_strict_usize(dot_product_columns[0].len());

    let mut prover_state = build_prover_state::<EF>();
    prover_state.add_base_scalars(
        &[
            log_n_cycles,
            n_poseidons_16,
            n_poseidons_24,
            dot_products.len(),
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
            F::from_usize(vm_multilinear_eval.n_vars),
        ]);
        prover_state.add_extension_scalars(&vm_multilinear_eval.point);
        prover_state.add_extension_scalar(vm_multilinear_eval.res);
    }

    let mut memory_statements = vec![];
    for multilinear_eval in &vm_multilinear_evals {
        let addr_point = multilinear_eval.addr_point;
        let addr_coeffs = multilinear_eval.addr_coeffs;
        let addr_res = multilinear_eval.addr_res;

        // point lookup into memory
        let log_point_len = log2_ceil_usize(multilinear_eval.point.len() * DIMENSION);
        let point_random_challenge = prover_state.sample_vec(log_point_len);
        let point_random_value = {
            let mut point_mle = multilinear_eval
                .point
                .iter()
                .flat_map(|v| {
                    <EF as BasedVectorSpace<PF<EF>>>::as_basis_coefficients_slice(v).to_vec()
                })
                .collect::<Vec<_>>();
            point_mle.resize(point_mle.len().next_power_of_two(), F::ZERO);
            point_mle.evaluate(&MultilinearPoint(point_random_challenge.clone()))
        };
        memory_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    to_big_endian_in_field(addr_point, log_memory - log_point_len),
                    point_random_challenge.clone(),
                ]
                .concat(),
            ),
            value: point_random_value,
        });

        // result lookup into memory
        let res_random_challenge = prover_state.sample_vec(LOG_VECTOR_LEN);
        let res_random_value = {
            let mut res_mle = multilinear_eval.res.as_basis_coefficients_slice().to_vec();
            res_mle.resize(VECTOR_LEN, F::ZERO);
            res_mle.evaluate(&MultilinearPoint(res_random_challenge.clone()))
        };
        memory_statements.push(Evaluation {
            point: MultilinearPoint(
                [
                    to_big_endian_in_field(addr_res, log_memory - LOG_VECTOR_LEN),
                    res_random_challenge.clone(),
                ]
                .concat(),
            ),
            value: res_random_value,
        });

        {
            let n_vars = multilinear_eval.n_vars;
            assert!(n_vars <= log_memory);
            assert!(addr_coeffs < 1 << (log_memory - n_vars));

            let addr_bits = to_big_endian_in_field(addr_coeffs, log_memory - n_vars);
            let statement = Evaluation {
                point: MultilinearPoint([addr_bits, multilinear_eval.point.clone()].concat()),
                value: multilinear_eval.res,
            };
            memory_statements.push(statement);
        }
    }
    let p16_indexes = all_poseidon_16_indexes(&poseidons_16);
    let p24_indexes = all_poseidon_24_indexes(&poseidons_24);

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory.len(),
        bytecode.ending_pc,
        n_poseidons_16,
        n_poseidons_24,
        p16_air.width(),
        p24_air.width(),
        n_rows_table_dot_products,
    );

    let dot_product_col_index_a = field_slice_as_base(&dot_product_columns[2]).unwrap();
    let dot_product_col_index_b = field_slice_as_base(&dot_product_columns[3]).unwrap();
    let dot_product_col_index_res = field_slice_as_base(&dot_product_columns[4]).unwrap();

    let base_pols = [
        vec![
            padded_memory.as_slice(),
            full_trace[COL_INDEX_PC].as_slice(),
            full_trace[COL_INDEX_FP].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_A].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_B].as_slice(),
            full_trace[COL_INDEX_MEM_ADDRESS_C].as_slice(),
            p16_indexes[0].as_slice(),
            p16_indexes[1].as_slice(),
            p16_indexes[2].as_slice(),
            p24_indexes[0].as_slice(),
            p24_indexes[1].as_slice(),
            p24_indexes[2].as_slice(),
        ],
        p16_columns[16..p16_air.width() - 16]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        p24_columns[24..p24_air.width() - 24]
            .iter()
            .map(Vec::as_slice)
            .collect::<Vec<_>>(),
        vec![
            dot_product_flags.as_slice(),
            dot_product_lengths.as_slice(),
            dot_product_col_index_a.as_slice(),
            dot_product_col_index_b.as_slice(),
            dot_product_col_index_res.as_slice(),
        ],
        dot_product_computations_base
            .iter()
            .map(Vec::as_slice)
            .collect(),
    ]
    .concat();

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(
        pcs.pcs_a(),
        &base_pols,
        &base_dims,
        &dft,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    // Grand Product for consistency with precompiles
    let grand_product_challenge_global = prover_state.sample();
    let grand_product_challenge_p16 = prover_state.sample().powers().collect_n(5);
    let grand_product_challenge_p24 = prover_state.sample().powers().collect_n(5);
    let grand_product_challenge_dot_product = prover_state.sample().powers().collect_n(6);
    let grand_product_challenge_vm_multilinear_eval = prover_state.sample().powers().collect_n(6);
    let mut exec_column_for_grand_product = vec![grand_product_challenge_global; n_cycles];
    for pos16 in &poseidons_16 {
        let Some(cycle) = pos16.cycle else {
            break;
        };
        exec_column_for_grand_product[cycle] = grand_product_challenge_global
            + grand_product_challenge_p16[1]
            + grand_product_challenge_p16[2] * F::from_usize(pos16.addr_input_a)
            + grand_product_challenge_p16[3] * F::from_usize(pos16.addr_input_b)
            + grand_product_challenge_p16[4] * F::from_usize(pos16.addr_output);
    }
    for pos24 in &poseidons_24 {
        let Some(cycle) = pos24.cycle else {
            break;
        };
        exec_column_for_grand_product[cycle] = grand_product_challenge_global
            + grand_product_challenge_p24[1]
            + grand_product_challenge_p24[2] * F::from_usize(pos24.addr_input_a)
            + grand_product_challenge_p24[3] * F::from_usize(pos24.addr_input_b)
            + grand_product_challenge_p24[4] * F::from_usize(pos24.addr_output);
    }
    for dot_product in &dot_products {
        exec_column_for_grand_product[dot_product.cycle] = grand_product_challenge_global
            + grand_product_challenge_dot_product[1]
            + grand_product_challenge_dot_product[2] * F::from_usize(dot_product.addr_0)
            + grand_product_challenge_dot_product[3] * F::from_usize(dot_product.addr_1)
            + grand_product_challenge_dot_product[4] * F::from_usize(dot_product.addr_res)
            + grand_product_challenge_dot_product[5] * F::from_usize(dot_product.len);
    }
    for multilinear_eval in &vm_multilinear_evals {
        exec_column_for_grand_product[multilinear_eval.cycle] = grand_product_challenge_global
            + grand_product_challenge_vm_multilinear_eval[1]
            + grand_product_challenge_vm_multilinear_eval[2]
                * F::from_usize(multilinear_eval.addr_coeffs)
            + grand_product_challenge_vm_multilinear_eval[3]
                * F::from_usize(multilinear_eval.addr_point)
            + grand_product_challenge_vm_multilinear_eval[4]
                * F::from_usize(multilinear_eval.addr_res)
            + grand_product_challenge_vm_multilinear_eval[5]
                * F::from_usize(multilinear_eval.n_vars);
    }

    let (grand_product_exec_res, grand_product_exec_statement) = prove_gkr_product(
        &mut prover_state,
        pack_extension(&exec_column_for_grand_product),
    );

    let p16_column_for_grand_product = poseidons_16
        .par_iter()
        .map(|pos_16| {
            grand_product_challenge_global
                + grand_product_challenge_p16[1]
                + grand_product_challenge_p16[2] * F::from_usize(pos_16.addr_input_a)
                + grand_product_challenge_p16[3] * F::from_usize(pos_16.addr_input_b)
                + grand_product_challenge_p16[4] * F::from_usize(pos_16.addr_output)
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
                + grand_product_challenge_p24[1]
                + grand_product_challenge_p24[2] * F::from_usize(pos_24.addr_input_a)
                + grand_product_challenge_p24[3] * F::from_usize(pos_24.addr_input_b)
                + grand_product_challenge_p24[4] * F::from_usize(pos_24.addr_output)
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
                + grand_product_challenge_dot_product[1]
                + (grand_product_challenge_dot_product[2] * dot_product_columns[2][i]
                    + grand_product_challenge_dot_product[3] * dot_product_columns[3][i]
                    + grand_product_challenge_dot_product[4] * dot_product_columns[4][i]
                    + grand_product_challenge_dot_product[5] * dot_product_columns[1][i])
                    * dot_product_columns[0][i]
        })
        .collect::<Vec<_>>();

    let vm_multilinear_eval_grand_product_res = vm_multilinear_evals
        .iter()
        .map(|vm_multilinear_eval| {
            grand_product_challenge_global
                + grand_product_challenge_vm_multilinear_eval[1]
                + grand_product_challenge_vm_multilinear_eval[2]
                    * F::from_usize(vm_multilinear_eval.addr_coeffs)
                + grand_product_challenge_vm_multilinear_eval[3]
                    * F::from_usize(vm_multilinear_eval.addr_point)
                + grand_product_challenge_vm_multilinear_eval[4]
                    * F::from_usize(vm_multilinear_eval.addr_res)
                + grand_product_challenge_vm_multilinear_eval[5]
                    * F::from_usize(vm_multilinear_eval.n_vars)
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
        p16_indexes[0].evaluate(&grand_product_p16_statement.point);
    let p16_grand_product_evals_on_indexes_b =
        p16_indexes[1].evaluate(&grand_product_p16_statement.point);
    let p16_grand_product_evals_on_indexes_res =
        p16_indexes[2].evaluate(&grand_product_p16_statement.point);
    prover_state.add_extension_scalars(&[
        p16_grand_product_evals_on_indexes_a,
        p16_grand_product_evals_on_indexes_b,
        p16_grand_product_evals_on_indexes_res,
    ]);

    let mut p16_indexes_a_statements = vec![Evaluation {
        point: grand_product_p16_statement.point.clone(),
        value: p16_grand_product_evals_on_indexes_a,
    }];
    let mut p16_indexes_b_statements = vec![Evaluation {
        point: grand_product_p16_statement.point.clone(),
        value: p16_grand_product_evals_on_indexes_b,
    }];
    let mut p16_indexes_res_statements = vec![Evaluation {
        point: grand_product_p16_statement.point.clone(),
        value: p16_grand_product_evals_on_indexes_res,
    }];

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

    let mut p24_indexes_a_statements = vec![Evaluation {
        point: grand_product_p24_statement.point.clone(),
        value: p24_grand_product_evals_on_indexes_a,
    }];
    let mut p24_indexes_b_statements = vec![Evaluation {
        point: grand_product_p24_statement.point.clone(),
        value: p24_grand_product_evals_on_indexes_b,
    }];
    let mut p24_indexes_res_statements = vec![Evaluation {
        point: grand_product_p24_statement.point.clone(),
        value: p24_grand_product_evals_on_indexes_res,
    }];

    let dot_product_footprint_computation = DotProductFootprint {
        grand_product_challenge_global,
        grand_product_challenge_dot_product: grand_product_challenge_dot_product
            .clone()
            .try_into()
            .unwrap(),
    };

    let (
        grand_product_dot_product_sumcheck_point,
        grand_product_dot_product_sumcheck_inner_evals,
        _,
    ) = sumcheck::prove(
        1, // TODO univariate skip?
        MleGroupRef::Extension(
            dot_product_columns[..5]
                .iter()
                .map(|c| c.as_slice())
                .collect::<Vec<_>>(),
        ), // TODO packing
        &dot_product_footprint_computation,
        &dot_product_footprint_computation,
        &[],
        Some((grand_product_dot_product_statement.point.0.clone(), None)),
        false,
        &mut prover_state,
        grand_product_dot_product_statement.value,
        None,
    );
    assert_eq!(grand_product_dot_product_sumcheck_inner_evals.len(), 5);
    prover_state.add_extension_scalars(&grand_product_dot_product_sumcheck_inner_evals);

    let grand_product_dot_product_flag_statement = Evaluation {
        point: grand_product_dot_product_sumcheck_point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[0],
    };

    let grand_product_dot_product_len_statement = Evaluation {
        point: grand_product_dot_product_sumcheck_point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[1],
    };

    let grand_product_dot_product_table_indexes_statement_index_a = Evaluation {
        point: grand_product_dot_product_sumcheck_point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[2],
    };
    let grand_product_dot_product_table_indexes_statement_index_b = Evaluation {
        point: grand_product_dot_product_sumcheck_point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[3],
    };
    let grand_product_dot_product_table_indexes_statement_index_res = Evaluation {
        point: grand_product_dot_product_sumcheck_point.clone(),
        value: grand_product_dot_product_sumcheck_inner_evals[4],
    };

    let precompile_foot_print_computation = PrecompileFootprint {
        grand_product_challenge_global,
        grand_product_challenge_p16: grand_product_challenge_p16.try_into().unwrap(),
        grand_product_challenge_p24: grand_product_challenge_p24.try_into().unwrap(),
        grand_product_challenge_dot_product: grand_product_challenge_dot_product
            .try_into()
            .unwrap(),
        grand_product_challenge_vm_multilinear_eval: grand_product_challenge_vm_multilinear_eval
            .try_into()
            .unwrap(),
    };

    let (grand_product_exec_sumcheck_point, grand_product_exec_sumcheck_inner_evals, _) =
        sumcheck::prove(
            1, // TODO univariate skip?
            MleGroupRef::Base(
                // TODO not all columns re required
                full_trace.iter().map(|c| c.as_slice()).collect::<Vec<_>>(),
            ), // TODO packing
            &precompile_foot_print_computation,
            &precompile_foot_print_computation,
            &[],
            Some((grand_product_exec_statement.point.0.clone(), None)),
            false,
            &mut prover_state,
            grand_product_exec_statement.value,
            None,
        );

    prover_state.add_extension_scalars(&grand_product_exec_sumcheck_inner_evals);
    assert_eq!(
        N_TOTAL_COLUMNS,
        grand_product_exec_sumcheck_inner_evals.len()
    ); // TODO open less columns

    let grand_product_exec_evals_on_each_column =
        &grand_product_exec_sumcheck_inner_evals[..N_INSTRUCTION_COLUMNS];

    let grand_product_fp_statement = Evaluation {
        point: grand_product_exec_sumcheck_point.clone(),
        value: grand_product_exec_sumcheck_inner_evals[COL_INDEX_FP],
    };

    let exec_evals_to_prove = info_span!("Execution AIR proof")
        .in_scope(|| exec_table.prove_base(&mut prover_state, UNIVARIATE_SKIPS, exec_witness));

    let dot_product_evals_to_prove = info_span!("DotProduct AIR proof")
        .in_scope(|| dot_product_table.prove_extension(&mut prover_state, 1, dot_product_witness));

    let p16_evals_to_prove = info_span!("Poseidon-16 AIR proof")
        .in_scope(|| p16_table.prove_base(&mut prover_state, UNIVARIATE_SKIPS, p16_witness));

    let p24_evals_to_prove = info_span!("Poseidon-24 AIR proof")
        .in_scope(|| p24_table.prove_base(&mut prover_state, UNIVARIATE_SKIPS, p24_witness));

    let max_n_poseidons = poseidons_16
        .len()
        .max(poseidons_24.len())
        .next_power_of_two();
    let (
        all_poseidon_indexes,
        folded_memory,
        poseidon_pushforward,
        poseidon_lookup_statements,
        poseidon_poly_eq_point,
        memory_folding_challenges,
        poseidon_logup_star_alpha,
    ) = {
        // Poseidons 16/24 memory addresses lookup
        let poseidon_logup_star_alpha = prover_state.sample();
        let memory_folding_challenges = MultilinearPoint(prover_state.sample_vec(LOG_VECTOR_LEN));

        let p16_lookup_point = p16_evals_to_prove[0].point.0.clone();
        let p24_lookup_point = p24_evals_to_prove[0].point.0.clone();

        #[rustfmt::skip]
        let p16_folded_eval_addr_a = p16_evals_to_prove[..8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p16_folded_eval_addr_b = p16_evals_to_prove[8..16].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p16_folded_eval_addr_res_a = p16_evals_to_prove[p16_air.width() - 16..p16_air.width() - 8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p16_folded_eval_addr_res_b = p16_evals_to_prove[p16_air.width() - 8..].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);

        #[rustfmt::skip]
        let p24_folded_eval_addr_a = p24_evals_to_prove[..8].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p24_folded_eval_addr_b = p24_evals_to_prove[8..16].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p24_folded_eval_addr_c = p24_evals_to_prove[16..24].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);
        #[rustfmt::skip]
        let p24_folded_eval_addr_res = p24_evals_to_prove[p24_air.width() - 8..].iter().map(|s| s.value).collect::<Vec<_>>().evaluate(&memory_folding_challenges);

        let padding_p16 =
            EF::zero_vec(log2_ceil_usize(max_n_poseidons) - log2_ceil_usize(n_poseidons_16));
        let padding_p24 =
            EF::zero_vec(log2_ceil_usize(max_n_poseidons) - log2_ceil_usize(n_poseidons_24));

        let poseidon_lookup_statements = vec![
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ZERO; 3],
                        padding_p16.clone(),
                        p16_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p16_folded_eval_addr_a,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ZERO, EF::ZERO, EF::ONE],
                        padding_p16.clone(),
                        p16_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p16_folded_eval_addr_b,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ZERO, EF::ONE, EF::ZERO],
                        padding_p16.clone(),
                        p16_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p16_folded_eval_addr_res_a,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ZERO, EF::ONE, EF::ONE],
                        padding_p16.clone(),
                        p16_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p16_folded_eval_addr_res_b,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ONE, EF::ZERO, EF::ZERO],
                        padding_p24.clone(),
                        p24_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p24_folded_eval_addr_a,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ONE, EF::ZERO, EF::ONE],
                        padding_p24.clone(),
                        p24_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p24_folded_eval_addr_b,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ONE, EF::ONE, EF::ZERO],
                        padding_p24.clone(),
                        p24_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p24_folded_eval_addr_c,
            },
            Evaluation {
                point: MultilinearPoint(
                    [
                        vec![EF::ONE, EF::ONE, EF::ONE],
                        padding_p24.clone(),
                        p24_lookup_point.clone(),
                    ]
                    .concat(),
                ),
                value: p24_folded_eval_addr_res,
            },
        ];

        let mut all_poseidon_indexes = F::zero_vec(8 * max_n_poseidons);
        #[rustfmt::skip]
        let chunks = [
            poseidons_16.par_iter().map(|p| p.addr_input_a).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| p.addr_input_b).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| p.addr_output).collect::<Vec<_>>(),
            poseidons_16.par_iter().map(|p| p.addr_output + 1).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_a).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_a + 1).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_input_b).collect::<Vec<_>>(),
            poseidons_24.par_iter().map(|p| p.addr_output).collect::<Vec<_>>()
        ];
        for (chunk_idx, addrs) in chunks.into_iter().enumerate() {
            all_poseidon_indexes[chunk_idx * max_n_poseidons..]
                .par_iter_mut()
                .zip(addrs)
                .for_each(|(slot, addr)| {
                    *slot = F::from_usize(addr);
                });
        }

        let poseidon_folded_memory = fold_multilinear(&padded_memory, &memory_folding_challenges);

        let mut poseidon_poly_eq_point = EF::zero_vec(max_n_poseidons * 8);
        for (i, statement) in poseidon_lookup_statements.iter().enumerate() {
            compute_sparse_eval_eq::<PF<EF>, EF>(
                &statement.point,
                &mut poseidon_poly_eq_point,
                poseidon_logup_star_alpha.exp_u64(i as u64),
            );
        }

        let poseidon_pushforward = compute_pushforward(
            &all_poseidon_indexes,
            poseidon_folded_memory.len(),
            &poseidon_poly_eq_point,
        );

        (
            all_poseidon_indexes,
            poseidon_folded_memory,
            poseidon_pushforward,
            poseidon_lookup_statements,
            poseidon_poly_eq_point,
            memory_folding_challenges,
            poseidon_logup_star_alpha,
        )
    };

    for i in 1..N_INSTRUCTION_COLUMNS_IN_AIR {
        assert_eq!(&exec_evals_to_prove[0].point, &exec_evals_to_prove[i].point);
    }
    let bytecode_lookup_point_1 = exec_evals_to_prove[0].point.clone();
    let non_used_precompiles_evals = full_trace
        [N_INSTRUCTION_COLUMNS_IN_AIR..N_INSTRUCTION_COLUMNS]
        .iter()
        .map(|col| col.evaluate(&bytecode_lookup_point_1))
        .collect::<Vec<_>>();
    prover_state.add_extension_scalars(&non_used_precompiles_evals);
    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim_1 = Evaluation {
        point: bytecode_lookup_point_1.clone(),
        value: padd_with_zero_to_next_power_of_two(
            &[
                (0..N_INSTRUCTION_COLUMNS_IN_AIR)
                    .map(|i| exec_evals_to_prove[i].value)
                    .collect::<Vec<_>>(),
                non_used_precompiles_evals,
            ]
            .concat(),
        )
        .evaluate(&bytecode_compression_challenges),
    };
    let bytecode_lookup_point_2 = grand_product_exec_sumcheck_point.clone();
    let bytecode_lookup_claim_2 = Evaluation {
        point: bytecode_lookup_point_2.clone(),
        value: padd_with_zero_to_next_power_of_two(grand_product_exec_evals_on_each_column)
            .evaluate(&bytecode_compression_challenges),
    };
    let alpha_bytecode_lookup = prover_state.sample();

    let mut bytecode_poly_eq_point = eval_eq(&bytecode_lookup_point_1);
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

    let dot_product_table_length = dot_product_columns[0].len();
    assert!(dot_product_table_length.is_power_of_two());
    let mut dot_product_indexes_spread = vec![F::zero_vec(dot_product_table_length * 4); DIMENSION];
    for i in 0..dot_product_table_length {
        let index_a: F = dot_product_columns[2][i].as_base().unwrap();
        let index_b: F = dot_product_columns[3][i].as_base().unwrap();
        let index_res: F = dot_product_columns[4][i].as_base().unwrap();
        for j in 0..DIMENSION {
            dot_product_indexes_spread[j][i] = index_a + F::from_usize(j);
            dot_product_indexes_spread[j][i + dot_product_table_length] =
                index_b + F::from_usize(j);
            dot_product_indexes_spread[j][i + 2 * dot_product_table_length] =
                index_res + F::from_usize(j);
        }
    }
    let dot_product_values_spread = dot_product_indexes_spread
        .iter()
        .map(|slice| {
            slice
                .par_iter()
                .map(|i| memory[i.to_usize()])
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let dot_product_evals_spread = dot_product_values_spread
        .iter()
        .map(|slice| slice.evaluate(&dot_product_evals_to_prove[5].point))
        .collect::<Vec<_>>();
    assert_eq!(
        dot_product_with_base(&dot_product_evals_spread),
        dot_product_evals_to_prove[5].value
    );
    prover_state.add_extension_scalars(&dot_product_evals_spread);

    let dot_product_values_batching_scalars = MultilinearPoint(prover_state.sample_vec(3));

    let dot_product_values_batched_point = MultilinearPoint(
        [
            dot_product_values_batching_scalars.0.clone(),
            dot_product_evals_to_prove[5].point.0.clone(),
        ]
        .concat(),
    );
    let dot_product_values_batched_eval =
        padd_with_zero_to_next_power_of_two(&dot_product_evals_spread)
            .evaluate(&dot_product_values_batching_scalars);

    let concatenated_dot_product_values_spread =
        padd_with_zero_to_next_power_of_two(&dot_product_values_spread.concat());

    let padded_dot_product_indexes_spread =
        padd_with_zero_to_next_power_of_two(&dot_product_indexes_spread.concat());

    assert!(
        padded_dot_product_indexes_spread.len() <= 1 << log_n_cycles,
        "TODO a more general commitment structure"
    );

    let unused_1 = evaluate_as_larger_multilinear_pol(
        &concatenated_dot_product_values_spread,
        &grand_product_exec_sumcheck_point,
    );
    prover_state.add_extension_scalar(unused_1);

    let grand_product_mem_values_mixing_challenges = MultilinearPoint(prover_state.sample_vec(2));
    let base_memory_lookup_statement_1 = Evaluation {
        point: MultilinearPoint(
            [
                grand_product_mem_values_mixing_challenges.0.clone(),
                grand_product_exec_sumcheck_point.0,
            ]
            .concat(),
        ),
        value: [
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_A],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_B],
            grand_product_exec_sumcheck_inner_evals[COL_INDEX_MEM_VALUE_C],
            unused_1,
        ]
        .evaluate(&grand_product_mem_values_mixing_challenges),
    };

    assert_eq_many!(
        &exec_evals_to_prove[COL_INDEX_MEM_VALUE_A.index_in_air()].point,
        &exec_evals_to_prove[COL_INDEX_MEM_VALUE_B.index_in_air()].point,
        &exec_evals_to_prove[COL_INDEX_MEM_VALUE_C.index_in_air()].point
    );
    let unused_2 = evaluate_as_larger_multilinear_pol(
        &concatenated_dot_product_values_spread,
        &exec_evals_to_prove[COL_INDEX_MEM_VALUE_A.index_in_air()].point,
    );
    prover_state.add_extension_scalar(unused_2);
    let exec_air_mem_values_mixing_challenges = MultilinearPoint(prover_state.sample_vec(2));
    let base_memory_lookup_statement_2 = Evaluation {
        point: MultilinearPoint(
            [
                exec_air_mem_values_mixing_challenges.0.clone(),
                exec_evals_to_prove[COL_INDEX_MEM_VALUE_A.index_in_air()]
                    .point
                    .0
                    .clone(),
            ]
            .concat(),
        ),
        value: [
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_A.index_in_air()].value,
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_B.index_in_air()].value,
            exec_evals_to_prove[COL_INDEX_MEM_VALUE_C.index_in_air()].value,
            unused_2,
        ]
        .evaluate(&exec_air_mem_values_mixing_challenges),
    };

    let unused_3a = evaluate_as_smaller_multilinear_pol(
        &full_trace[COL_INDEX_MEM_VALUE_A],
        &dot_product_values_batched_point,
    );
    let unused_3b = evaluate_as_smaller_multilinear_pol(
        &full_trace[COL_INDEX_MEM_VALUE_B],
        &dot_product_values_batched_point,
    );
    let unused_3c = evaluate_as_smaller_multilinear_pol(
        &full_trace[COL_INDEX_MEM_VALUE_C],
        &dot_product_values_batched_point,
    );
    prover_state.add_extension_scalars(&[unused_3a, unused_3b, unused_3c]);

    let dot_product_air_mem_values_mixing_challenges = MultilinearPoint(prover_state.sample_vec(2));
    let base_memory_lookup_statement_3 = Evaluation {
        point: MultilinearPoint(
            [
                dot_product_air_mem_values_mixing_challenges.0.clone(),
                EF::zero_vec(log_n_cycles - dot_product_values_batched_point.len()),
                dot_product_values_batched_point.0.clone(),
            ]
            .concat(),
        ),
        value: [
            unused_3a,
            unused_3b,
            unused_3c,
            dot_product_values_batched_eval,
        ]
        .evaluate(&dot_product_air_mem_values_mixing_challenges),
    };

    // Main memory lookup
    let base_memory_indexes = [
        full_trace[COL_INDEX_MEM_ADDRESS_A].clone(),
        full_trace[COL_INDEX_MEM_ADDRESS_B].clone(),
        full_trace[COL_INDEX_MEM_ADDRESS_C].clone(),
        [
            padded_dot_product_indexes_spread.clone(),
            F::zero_vec((1 << log_n_cycles) - padded_dot_product_indexes_spread.len()),
        ]
        .concat(),
    ]
    .concat();

    let memory_poly_eq_point_alpha = prover_state.sample();

    let mut base_memory_poly_eq_point = eval_eq(&base_memory_lookup_statement_1.point);
    compute_eval_eq::<PF<EF>, EF, true>(
        &base_memory_lookup_statement_2.point,
        &mut base_memory_poly_eq_point,
        memory_poly_eq_point_alpha,
    );
    compute_eval_eq::<PF<EF>, EF, true>(
        &base_memory_lookup_statement_3.point,
        &mut base_memory_poly_eq_point,
        memory_poly_eq_point_alpha.square(),
    );
    let base_memory_pushforward = compute_pushforward(
        &base_memory_indexes,
        padded_memory.len(),
        &base_memory_poly_eq_point,
    );

    // 2nd Commitment
    let extension_pols = vec![
        base_memory_pushforward.as_slice(),
        poseidon_pushforward.as_slice(),
        bytecode_pushforward.as_slice(),
    ];

    let extension_dims = vec![
        ColDims::sparse(memory.len(), EF::ZERO), // memory
        ColDims::sparse(memory.len().div_ceil(VECTOR_LEN), EF::ZERO), // memory (folded)
        ColDims::sparse(bytecode.instructions.len(), EF::ZERO), // bytecode
    ];

    let packed_pcs_witness_extension = packed_pcs_commit(
        &pcs.pcs_b(
            log2_strict_usize(packed_pcs_witness_base.packed_polynomial.len()),
            num_packed_vars_for_dims::<EF, EF>(&extension_dims, LOG_SMALLEST_DECOMPOSITION_CHUNK),
        ),
        &extension_pols,
        &extension_dims,
        &dft,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let base_memory_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &padded_memory,
        &base_memory_indexes,
        base_memory_lookup_statement_1.value
            + memory_poly_eq_point_alpha * base_memory_lookup_statement_2.value
            + memory_poly_eq_point_alpha.square() * base_memory_lookup_statement_3.value,
        &base_memory_poly_eq_point,
        &base_memory_pushforward,
    );

    let poseidon_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &folded_memory,
        &all_poseidon_indexes,
        poseidon_lookup_statements
            .iter()
            .enumerate()
            .map(|(i, s)| s.value * poseidon_logup_star_alpha.exp_u64(i as u64))
            .sum(),
        &poseidon_poly_eq_point,
        &poseidon_pushforward,
    );

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &folded_bytecode,
        &full_trace[COL_INDEX_PC],
        bytecode_lookup_claim_1.value + alpha_bytecode_lookup * bytecode_lookup_claim_2.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward,
    );

    let poseidon_lookup_memory_point = MultilinearPoint(
        [
            poseidon_logup_star_statements.on_table.point.0.clone(),
            memory_folding_challenges.0,
        ]
        .concat(),
    );

    memory_statements.push(base_memory_logup_star_statements.on_table.clone());
    memory_statements.push(Evaluation {
        point: poseidon_lookup_memory_point.clone(),
        value: poseidon_logup_star_statements.on_table.value,
    });

    {
        // index opening for poseidon lookup

        let log_n_p16 = log2_ceil_usize(n_poseidons_16);
        let log_n_p24 = log2_ceil_usize(n_poseidons_24);
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

        let poseidon_index_evals = fold_multilinear(
            &all_poseidon_indexes,
            &MultilinearPoint(poseidon_logup_star_statements.on_indexes.point[3..].to_vec()),
        );
        let inner_values = [
            poseidon_index_evals[0] / correcting_factor_p16,
            poseidon_index_evals[1] / correcting_factor_p16,
            poseidon_index_evals[2] / correcting_factor_p16,
            // skip 3
            poseidon_index_evals[4] / correcting_factor_p24,
            // skip 5
            poseidon_index_evals[6] / correcting_factor_p24,
            poseidon_index_evals[7] / correcting_factor_p24,
        ];

        assert_eq!(
            poseidon_index_evals[3] / correcting_factor_p16,
            poseidon_index_evals[2] / correcting_factor_p16 + F::ONE
        );

        assert_eq!(
            poseidon_index_evals[5] / correcting_factor_p24,
            poseidon_index_evals[4] / correcting_factor_p24 + F::ONE
        );

        prover_state.add_extension_scalars(&inner_values);
        p16_indexes_a_statements.push(Evaluation {
            point: idx_point_right_p16.clone(),
            value: inner_values[0],
        });
        p16_indexes_b_statements.push(Evaluation {
            point: idx_point_right_p16.clone(),
            value: inner_values[1],
        });
        p16_indexes_res_statements.push(Evaluation {
            point: idx_point_right_p16.clone(),
            value: inner_values[2],
        });
        p24_indexes_a_statements.push(Evaluation {
            point: idx_point_right_p24.clone(),
            value: inner_values[3],
        });
        p24_indexes_b_statements.push(Evaluation {
            point: idx_point_right_p24.clone(),
            value: inner_values[4],
        });
        p24_indexes_res_statements.push(Evaluation {
            point: idx_point_right_p24.clone(),
            value: inner_values[5],
        });

        // sanity check
        assert_eq!(
            poseidon_index_evals.evaluate(&MultilinearPoint(
                poseidon_logup_star_statements.on_indexes.point[..3].to_vec()
            )),
            poseidon_logup_star_statements.on_indexes.value
        );
    }

    let (initial_pc_statement, final_pc_statement) =
        intitial_and_final_pc_conditions(bytecode, log_n_cycles);

    let dot_product_computation_column_evals = dot_product_computations_base
        .par_iter()
        .map(|slice| slice.evaluate(&dot_product_evals_to_prove[6].point))
        .collect::<Vec<_>>();
    assert_eq!(
        dot_product_with_base(&dot_product_computation_column_evals),
        dot_product_evals_to_prove[6].value
    );
    prover_state.add_extension_scalars(&dot_product_computation_column_evals);
    let dot_product_computation_column_statements = (0..DIMENSION)
        .map(|i| {
            vec![Evaluation {
                point: dot_product_evals_to_prove[6].point.clone(),
                value: dot_product_computation_column_evals[i],
            }]
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
    assert_eq!(
        log2_strict_usize(padded_dot_product_indexes_spread.len()),
        log_n_rows_dot_product_table + 5
    );
    let index_diff = log_n_cycles - log2_strict_usize(padded_dot_product_indexes_spread.len());
    let mem_lookup_eval_spread_indexes_dot_product = padded_dot_product_indexes_spread.evaluate(
        &MultilinearPoint(mem_lookup_eval_indexes_partial_point[index_diff..].to_vec()),
    );

    prover_state.add_extension_scalars(&[
        mem_lookup_eval_indexes_a,
        mem_lookup_eval_indexes_b,
        mem_lookup_eval_indexes_c,
        mem_lookup_eval_spread_indexes_dot_product,
    ]);

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
    let dot_product_logup_star_indexes_inner_value_a =
        dot_product_columns[2].evaluate(&dot_product_logup_star_indexes_inner_point);
    let dot_product_logup_star_indexes_inner_value_b =
        dot_product_columns[3].evaluate(&dot_product_logup_star_indexes_inner_point);
    let dot_product_logup_star_indexes_inner_value_res =
        dot_product_columns[4].evaluate(&dot_product_logup_star_indexes_inner_point);

    prover_state.add_extension_scalars(&[
        dot_product_logup_star_indexes_inner_value_a,
        dot_product_logup_star_indexes_inner_value_b,
        dot_product_logup_star_indexes_inner_value_res,
    ]);

    let dot_product_logup_star_indexes_statement_a = Evaluation {
        point: dot_product_logup_star_indexes_inner_point.clone(),
        value: dot_product_logup_star_indexes_inner_value_a,
    };
    let dot_product_logup_star_indexes_statement_b = Evaluation {
        point: dot_product_logup_star_indexes_inner_point.clone(),
        value: dot_product_logup_star_indexes_inner_value_b,
    };
    let dot_product_logup_star_indexes_statement_res = Evaluation {
        point: dot_product_logup_star_indexes_inner_point.clone(),
        value: dot_product_logup_star_indexes_inner_value_res,
    };

    // First Opening
    let global_statements_base = packed_pcs_global_statements_for_prover(
        &base_pols,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            vec![
                memory_statements,
                vec![
                    exec_evals_to_prove[COL_INDEX_PC.index_in_air()].clone(),
                    bytecode_logup_star_statements.on_indexes.clone(),
                    initial_pc_statement,
                    final_pc_statement,
                ], // pc
                vec![
                    exec_evals_to_prove[COL_INDEX_FP.index_in_air()].clone(),
                    grand_product_fp_statement,
                ], // fp
                vec![
                    exec_evals_to_prove[COL_INDEX_MEM_ADDRESS_A.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point.clone(),
                        value: mem_lookup_eval_indexes_a,
                    },
                ], // exec memory address A
                vec![
                    exec_evals_to_prove[COL_INDEX_MEM_ADDRESS_B.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point.clone(),
                        value: mem_lookup_eval_indexes_b,
                    },
                ], // exec memory address B
                vec![
                    exec_evals_to_prove[COL_INDEX_MEM_ADDRESS_C.index_in_air()].clone(),
                    Evaluation {
                        point: mem_lookup_eval_indexes_partial_point,
                        value: mem_lookup_eval_indexes_c,
                    },
                ], // exec memory address C
                p16_indexes_a_statements,
                p16_indexes_b_statements,
                p16_indexes_res_statements,
                p24_indexes_a_statements,
                p24_indexes_b_statements,
                p24_indexes_res_statements,
            ],
            p16_evals_to_prove[16..p16_air.width() - 16]
                .iter()
                .map(|e| vec![e.clone()])
                .collect(),
            p24_evals_to_prove[24..p24_air.width() - 24]
                .iter()
                .map(|e| vec![e.clone()])
                .collect(),
            vec![
                vec![
                    dot_product_evals_to_prove[0].clone(),
                    grand_product_dot_product_flag_statement,
                ], // dot product: (start) flag
                vec![
                    dot_product_evals_to_prove[1].clone(),
                    grand_product_dot_product_len_statement,
                ], // dot product: length
                vec![
                    dot_product_evals_to_prove[2].clone(), // // dot product: indexe a
                    dot_product_logup_star_indexes_statement_a,
                    grand_product_dot_product_table_indexes_statement_index_a,
                ],
                vec![
                    dot_product_evals_to_prove[3].clone(), // // dot product: indexe b
                    dot_product_logup_star_indexes_statement_b,
                    grand_product_dot_product_table_indexes_statement_index_b,
                ],
                vec![
                    dot_product_evals_to_prove[4].clone(), // // dot product: indexe res
                    dot_product_logup_star_indexes_statement_res,
                    grand_product_dot_product_table_indexes_statement_index_res,
                ],
            ],
            dot_product_computation_column_statements,
        ]
        .concat(),
        &mut prover_state,
    );

    // Second Opening
    let global_statements_extension = packed_pcs_global_statements_for_prover(
        &extension_pols,
        &extension_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &[
            base_memory_logup_star_statements.on_pushforward,
            poseidon_logup_star_statements.on_pushforward,
            bytecode_logup_star_statements.on_pushforward,
        ],
        &mut prover_state,
    );

    pcs.batch_open(
        &dft,
        &mut prover_state,
        &global_statements_base,
        packed_pcs_witness_base.inner_witness,
        &packed_pcs_witness_base.packed_polynomial,
        &global_statements_extension,
        packed_pcs_witness_extension.inner_witness,
        &packed_pcs_witness_extension.packed_polynomial,
    );

    (
        prover_state.proof_data().to_vec(),
        prover_state.proof_size(),
    )
}
