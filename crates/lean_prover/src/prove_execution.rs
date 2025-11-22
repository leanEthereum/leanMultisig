use crate::common::*;
use crate::*;
use air::prove_air;
use lean_vm::*;
use lookup::{compute_pushforward, prove_gkr_quotient, prove_logup_star};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use poseidon_circuit::{PoseidonGKRLayers, prove_poseidon_gkr};
use sub_protocols::*;
use tracing::info_span;
use utils::{build_prover_state, padd_with_zero_to_next_power_of_two};
use whir_p3::{WhirConfig, WhirConfigBuilder, second_batched_whir_config_builder};
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
        n_cycles,
        traces,
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
    let log_public_memory = log2_strict_usize(public_memory.len());

    let log_n_cycles = log2_ceil_usize(n_cycles);
    assert!(
        traces[TABLE_EXECUTION]
            .base
            .iter()
            .all(|col| col.len() == 1 << log_n_cycles)
    );

    let log_n_p16 = log2_ceil_usize(traces[TABLE_POSEIDON_16].n_rows_non_padded())
        .max(MIN_LOG_N_ROWS_PER_TABLE);
    let log_n_p24 = log2_ceil_usize(traces[TABLE_POSEIDON_24].n_rows_non_padded())
        .max(MIN_LOG_N_ROWS_PER_TABLE);

    let _validity_proof_span = info_span!("Validity proof generation").entered();

    let p16_gkr_layers = PoseidonGKRLayers::<16, N_COMMITED_CUBES_P16>::build(Some(VECTOR_LEN));
    let p24_gkr_layers = PoseidonGKRLayers::<24, N_COMMITED_CUBES_P24>::build(None);

    let p16_witness = generate_poseidon_witness_helper(
        &p16_gkr_layers,
        &traces[TABLE_POSEIDON_16],
        POSEIDON_16_COL_INDEX_INPUT_START,
        Some(&traces[TABLE_POSEIDON_16].base[POSEIDON_16_COL_INDEX_COMPRESSION].clone()),
    );
    let p24_witness = generate_poseidon_witness_helper(
        &p24_gkr_layers,
        &traces[TABLE_POSEIDON_24],
        POSEIDON_24_COL_INDEX_INPUT_START,
        None,
    );

    let dot_product_computation_ext_base_helper =
        ExtensionCommitmentFromBaseProver::before_commitment(
            Table::dot_product()
                .commited_columns_ef()
                .iter()
                .map(|&c| &traces[TABLE_DOT_PRODUCT].ext[c][..])
                .collect::<Vec<_>>(),
        );

    let mut prover_state = build_prover_state::<EF>();
    prover_state.add_base_scalars(
        &[
            n_cycles,
            traces[TABLE_POSEIDON_16].n_rows_non_padded(),
            traces[TABLE_POSEIDON_24].n_rows_non_padded(),
            traces[TABLE_DOT_PRODUCT].n_rows_non_padded(),
            private_memory.len(),
        ]
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );

    let base_dims = get_base_dims(
        n_cycles,
        log_public_memory,
        private_memory.len(),
        traces[TABLE_POSEIDON_16].n_rows_non_padded(),
        traces[TABLE_POSEIDON_24].n_rows_non_padded(),
        traces[TABLE_DOT_PRODUCT].n_rows_non_padded(),
        (&p16_gkr_layers, &p24_gkr_layers),
    );

    let base_pols = [
        vec![memory.as_slice()],
        Table::execution().committed_columns(&traces[TABLE_EXECUTION], None),
        Table::poseidon16().committed_columns(&traces[TABLE_POSEIDON_16], None),
        p16_witness
            .committed_cubes
            .iter()
            .map(|s| FPacking::<F>::unpack_slice(s))
            .collect::<Vec<_>>(),
        Table::poseidon24().committed_columns(&traces[TABLE_POSEIDON_24], None),
        p24_witness
            .committed_cubes
            .iter()
            .map(|s| FPacking::<F>::unpack_slice(s))
            .collect::<Vec<_>>(),
        Table::dot_product().committed_columns(
            &traces[TABLE_DOT_PRODUCT],
            Some(&dot_product_computation_ext_base_helper),
        ),
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

    let bus_challenge = prover_state.sample();
    let fingerprint_challenge = prover_state.sample();

    let mut bus_quotients: [EF; N_TABLES] = Default::default();
    let mut air_points: [MultilinearPoint<EF>; N_TABLES] = Default::default();
    let mut evals_f: [Vec<EF>; N_TABLES] = Default::default();
    let mut evals_ef: [Vec<EF>; N_TABLES] = Default::default();

    for table in ALL_TABLES {
        let i = table.index();
        (bus_quotients[i], air_points[i], evals_f[i], evals_ef[i]) = prove_bus_and_air(
            &mut prover_state,
            &table,
            &traces[i],
            bus_challenge,
            fingerprint_challenge,
        );
    }

    assert_eq!(bus_quotients.iter().copied().sum::<EF>(), EF::ZERO);

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim_1 = Evaluation::new(
        air_points[TABLE_EXECUTION].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[TABLE_EXECUTION][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_poly_eq_point = eval_eq(&air_points[TABLE_EXECUTION]);
    let bytecode_pushforward = compute_pushforward(
        &traces[TABLE_EXECUTION].base[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    );

    let normal_lookup_into_memory = NormalPackedLookupProver::step_1(
        &mut prover_state,
        &memory,
        [
            ExecutionTable.normal_lookup_index_columns_f(&traces[TABLE_EXECUTION]),
            DotProductPrecompile.normal_lookup_index_columns_f(&traces[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        [
            ExecutionTable.normal_lookup_index_columns_ef(&traces[TABLE_EXECUTION]),
            DotProductPrecompile.normal_lookup_index_columns_ef(&traces[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        [
            vec![n_cycles; Table::execution().num_normal_lookups_f()],
            vec![
                traces[TABLE_DOT_PRODUCT]
                    .n_rows_non_padded()
                    .max(MIN_N_ROWS_PER_TABLE);
                Table::dot_product().num_normal_lookups_f()
            ],
        ]
        .concat(),
        [
            vec![n_cycles; Table::execution().num_normal_lookups_ef()],
            vec![
                traces[TABLE_DOT_PRODUCT]
                    .n_rows_non_padded()
                    .max(MIN_N_ROWS_PER_TABLE);
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
            Table::execution().normal_lookup_f_value_columns(&traces[TABLE_EXECUTION]),
            Table::dot_product().normal_lookup_f_value_columns(&traces[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        [
            Table::execution().normal_lookup_ef_value_columns(&traces[TABLE_EXECUTION]),
            Table::dot_product().normal_lookup_ef_value_columns(&traces[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        [
            Table::execution().normal_lookups_statements_f(&air_points[TABLE_EXECUTION], &evals_f[TABLE_EXECUTION]),
            Table::dot_product()
                .normal_lookups_statements_f(&air_points[TABLE_DOT_PRODUCT], &evals_f[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        [
            Table::execution().normal_lookups_statements_ef(&air_points[TABLE_EXECUTION], &evals_ef[TABLE_EXECUTION]),
            Table::dot_product()
                .normal_lookups_statements_ef(&air_points[TABLE_DOT_PRODUCT], &evals_ef[TABLE_DOT_PRODUCT]),
        ]
        .concat(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let vectorized_lookup_into_memory = VectorizedPackedLookupProver::<_, VECTOR_LEN>::step_1(
        &mut prover_state,
        &memory,
        [
            Table::poseidon16().vector_lookup_index_columns(&traces[TABLE_POSEIDON_16]),
            Table::poseidon24().vector_lookup_index_columns(&traces[TABLE_POSEIDON_24]),
        ]
        .concat(),
        [
            vec![
                traces[TABLE_POSEIDON_16]
                    .n_rows_non_padded()
                    .max(MIN_N_ROWS_PER_TABLE);
                Table::poseidon16().num_vector_lookups()
            ],
            vec![
                traces[TABLE_POSEIDON_24]
                    .n_rows_non_padded()
                    .max(MIN_N_ROWS_PER_TABLE);
                Table::poseidon24().num_vector_lookups()
            ],
        ]
        .concat(),
        [
            Table::poseidon16().vector_lookup_default_indexes(),
            Table::poseidon24().vector_lookup_default_indexes(),
        ]
        .concat(),
        [
            Table::poseidon16().vector_lookup_values_columns(&traces[TABLE_POSEIDON_16]),
            Table::poseidon24().vector_lookup_values_columns(&traces[TABLE_POSEIDON_24]),
        ]
        .concat(),
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

    let mut normal_lookup_statements =
        normal_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let vectorized_lookup_statements =
        vectorized_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &traces[TABLE_EXECUTION].base[COL_INDEX_PC],
        bytecode_lookup_claim_1.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward,
        Some(bytecode.instructions.len()),
    );

    let memory_statements = vec![
        normal_lookup_statements.on_table.clone(),
        vectorized_lookup_statements.on_table.clone(),
    ];

    let mut p16_statements = Table::poseidon16().committed_statements_prover(
        &mut prover_state,
        &air_points[TABLE_POSEIDON_16],
        &evals_f[TABLE_POSEIDON_16],
        None,
        &mut vec![],
        &mut vec![],
    );
    let mut p24_statements = Table::poseidon24().committed_statements_prover(
        &mut prover_state,
        &air_points[TABLE_POSEIDON_24],
        &evals_f[TABLE_POSEIDON_24],
        None,
        &mut vec![],
        &mut vec![],
    );

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

    let mut exec_statements = Table::execution().committed_statements_prover(
        &mut prover_state,
        &air_points[TABLE_EXECUTION],
        &evals_f[TABLE_EXECUTION],
        None,
        &mut normal_lookup_statements.on_indexes_f,
        &mut normal_lookup_statements.on_indexes_ef,
    );
    exec_statements[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)].extend(vec![
        bytecode_logup_star_statements.on_indexes.clone(),
        initial_pc_statement,
        final_pc_statement,
    ]);

    let dot_product_statements = Table::dot_product().committed_statements_prover(
        &mut prover_state,
        &air_points[TABLE_DOT_PRODUCT],
        &evals_f[TABLE_DOT_PRODUCT],
        Some(&dot_product_computation_ext_base_helper),
        &mut normal_lookup_statements.on_indexes_f,
        &mut normal_lookup_statements.on_indexes_ef,
    );
    assert!(normal_lookup_statements.on_indexes_f.is_empty());
    assert!(normal_lookup_statements.on_indexes_ef.is_empty());

    // First Opening
    let all_base_statements = [
        vec![memory_statements],
        exec_statements,
        p16_statements,
        encapsulate_vec(p16_gkr.cubes_statements.split()),
        p24_statements,
        encapsulate_vec(p24_gkr.cubes_statements.split()),
        dot_product_statements,
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
            normal_lookup_statements.on_pushforward,
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

fn prove_bus_and_air(
    prover_state: &mut multilinear_toolkit::prelude::FSProver<EF, impl FSChallenger<EF>>,
    t: &Table,
    trace: &TableTrace,
    bus_challenge: EF,
    fingerprint_challenge: EF,
) -> (EF, MultilinearPoint<EF>, Vec<EF>, Vec<EF>) {
    if t.buses().len() != 1 {
        panic!("Multiple buses not yet supported");
    }
    let bus = &t.buses()[0];

    let bus_data = (0..trace.n_rows_padded())
        .into_par_iter()
        .map(|i| {
            bus_challenge
                + finger_print(
                    match &bus.table {
                        BusTable::Constant(table) => table.embed(),
                        BusTable::Variable(col) => trace.base[*col][i],
                    },
                    bus.data
                        .iter()
                        .map(|col| trace.base[*col][i])
                        .collect::<Vec<_>>()
                        .as_slice(),
                    fingerprint_challenge,
                )
        })
        .collect::<Vec<_>>();

    // TODO embedding overhead !!!
    assert!(bus.selector < trace.base.len());
    let bus_selector = match bus.direction {
        BusDirection::Pull => trace.base[bus.selector]
            .par_iter()
            .map(|&x| EF::from(-x))
            .collect::<Vec<_>>(),
        BusDirection::Push => trace.base[bus.selector]
            .par_iter()
            .map(|&x| EF::from(x))
            .collect::<Vec<_>>(),
    };

    let bus_selector_packed = pack_extension(&bus_selector);
    let bus_data_packed = pack_extension(&bus_data);
    let (mut bus_quotient, bus_point, bus_selector_value, bus_data_value) =
        prove_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(
            prover_state,
            &MleGroupRef::ExtensionPacked(vec![&bus_selector_packed, &bus_data_packed]),
        );

    let bus_beta = prover_state.sample();
    let bus_final_value = bus_selector_value
        * match bus.direction {
            BusDirection::Pull => EF::NEG_ONE,
            BusDirection::Push => EF::ONE,
        }
        + bus_beta * bus_data_value;

    let bus_virtual_statement = MultiEvaluation::new(bus_point, vec![bus_final_value]);

    bus_quotient -=
        bus.padding_contribution(t, trace.padding_len, bus_challenge, fingerprint_challenge);

    let extra_data = ExtraDataForBuses {
        bus_challenge,
        fingerprint_challenge_powers: powers_const(fingerprint_challenge),
        bus_beta: bus_beta,
        alpha_powers: vec![], // filled later
    };
    let (air_point, evals_f, evals_ef) =
        info_span!("Table AIR proof", table = t.name()).in_scope(|| {
            macro_rules! prove_air_for_table {
                ($t:expr) => {
                    prove_air(
                        prover_state,
                        $t,
                        extra_data,
                        UNIVARIATE_SKIPS,
                        &trace.base[..$t.n_columns_f_air()],
                        &trace.ext[..$t.n_columns_ef_air()],
                        &$t.air_padding_row_f(),
                        &$t.air_padding_row_ef(),
                        Some(bus_virtual_statement),
                        $t.n_columns_air() + $t.total_n_down_columns_air() > 5, // heuristic
                    )
                };
            }
            delegate_to_inner!(t => prove_air_for_table)
        });

    (bus_quotient, air_point, evals_f, evals_ef)
}
