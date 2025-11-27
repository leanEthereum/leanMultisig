use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::prove_air;
use itertools::Itertools;
use lean_vm::*;
use lookup::{compute_pushforward, prove_gkr_quotient, prove_logup_star};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use p3_util::{log2_ceil_usize, log2_strict_usize};
use poseidon_circuit::{PoseidonGKRLayers, prove_poseidon_gkr};
use std::collections::VecDeque;
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
    merkle_path_hints: VecDeque<Vec<[F; 8]>>,
) -> (Proof<F>, String) {
    let mut exec_summary = String::new();
    let ExecutionTrace {
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
                merkle_path_hints,
            )
        });
        exec_summary = std::mem::take(&mut execution_result.summary);
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    if memory.len() < 1 << MIN_LOG_MEMORY_SIZE {
        memory.resize(1 << MIN_LOG_MEMORY_SIZE, F::ZERO);
        non_zero_memory_size = 1 << MIN_LOG_MEMORY_SIZE;
    }
    let public_memory = &memory[..public_memory_size];
    let private_memory = &memory[public_memory_size..non_zero_memory_size];
    let log_public_memory = log2_strict_usize(public_memory.len());

    let mut prover_state = build_prover_state::<EF>(false);
    prover_state.add_base_scalars(
        &[
            vec![private_memory.len()],
            traces.values().map(|t| t.n_rows_non_padded()).collect::<Vec<_>>(),
        ]
        .concat()
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );

    // only keep tables with non-zero rows
    let traces: BTreeMap<_, _> = traces
        .into_iter()
        .filter(|(table, trace)| {
            trace.n_rows_non_padded() > 0
                || table == &Table::execution()
                || table == &Table::poseidon16_core() // due to custom GKR
                || table == &Table::poseidon24() // due to custom GKR
        })
        .collect();

    let p16_gkr_layers = PoseidonGKRLayers::<16, N_COMMITED_CUBES_P16>::build(Some(VECTOR_LEN));
    let p24_gkr_layers = PoseidonGKRLayers::<24, N_COMMITED_CUBES_P24>::build(None);

    let p16_witness = generate_poseidon_witness_helper(
        &p16_gkr_layers,
        &traces[&Table::poseidon16_core()],
        POSEIDON_16_CORE_COL_INPUT_START,
        Some(&traces[&Table::poseidon16_core()].base[POSEIDON_16_CORE_COL_COMPRESSION].clone()),
    );
    let p24_witness = generate_poseidon_witness_helper(
        &p24_gkr_layers,
        &traces[&Table::poseidon24()],
        POSEIDON_24_COL_INDEX_INPUT_START,
        None,
    );

    let commitmenent_extension_helper = traces
        .iter()
        .filter(|(table, _)| table.n_commited_columns_ef() > 0)
        .map(|(table, trace)| {
            (
                *table,
                ExtensionCommitmentFromBaseProver::before_commitment(
                    table
                        .commited_columns_ef()
                        .iter()
                        .map(|&c| &trace.ext[c][..])
                        .collect::<Vec<_>>(),
                ),
            )
        })
        .collect::<BTreeMap<_, _>>();

    let base_dims = get_base_dims(
        log_public_memory,
        private_memory.len(),
        (&p16_gkr_layers, &p24_gkr_layers),
        &traces.iter().map(|(table, trace)| (*table, trace.height)).collect(),
    );

    let mut base_pols = [
        vec![memory.as_slice()],
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
    ]
    .concat();
    for (table, trace) in &traces {
        base_pols.extend(table.committed_columns(trace, commitmenent_extension_helper.get(table)));
    }

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(
        &whir_config_builder,
        &base_pols,
        &base_dims,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let random_point_p24 = MultilinearPoint(prover_state.sample_vec(traces[&Table::poseidon24()].log_padded()));
    let p24_gkr = prove_poseidon_gkr(
        &mut prover_state,
        &p24_witness,
        random_point_p24.0.clone(),
        UNIVARIATE_SKIPS,
        &p24_gkr_layers,
    );

    let bus_challenge = prover_state.sample();
    let fingerprint_challenge = prover_state.sample();

    let mut bus_quotients: BTreeMap<Table, EF> = Default::default();
    let mut air_points: BTreeMap<Table, MultilinearPoint<EF>> = Default::default();
    let mut evals_f: BTreeMap<Table, Vec<EF>> = Default::default();
    let mut evals_ef: BTreeMap<Table, Vec<EF>> = Default::default();

    for (table, trace) in &traces {
        let (this_bus_quotient, this_air_point, this_evals_f, this_evals_ef) =
            prove_bus_and_air(&mut prover_state, table, trace, bus_challenge, fingerprint_challenge);
        bus_quotients.insert(*table, this_bus_quotient);
        air_points.insert(*table, this_air_point);
        evals_f.insert(*table, this_evals_f);
        evals_ef.insert(*table, this_evals_ef);
    }

    assert_eq!(bus_quotients.values().copied().sum::<EF>(), EF::ZERO);

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim_1 = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[&Table::execution()][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_poly_eq_point = eval_eq(&air_points[&Table::execution()]);
    let bytecode_pushforward = compute_pushforward(
        &traces[&Table::execution()].base[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    );

    let normal_lookup_into_memory = NormalPackedLookupProver::step_1(
        &mut prover_state,
        &memory,
        traces
            .iter()
            .flat_map(|(table, trace)| table.normal_lookup_index_columns_f(trace))
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| table.normal_lookup_index_columns_ef(trace))
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| vec![trace.n_rows_non_padded_maxed(); table.num_normal_lookups_f()])
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| vec![trace.n_rows_non_padded_maxed(); table.num_normal_lookups_ef()])
            .collect(),
        traces
            .keys()
            .flat_map(|table| table.normal_lookup_default_indexes_f())
            .collect(),
        traces
            .keys()
            .flat_map(|table| table.normal_lookup_default_indexes_ef())
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| table.normal_lookup_f_value_columns(trace))
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| table.normal_lookup_ef_value_columns(trace))
            .collect(),
        traces
            .keys()
            .flat_map(|table| table.normal_lookups_statements_f(&air_points[table], &evals_f[table]))
            .collect(),
        traces
            .keys()
            .flat_map(|table| table.normal_lookups_statements_ef(&air_points[table], &evals_ef[table]))
            .collect(),
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let vectorized_lookup_into_memory = VectorizedPackedLookupProver::<_, VECTOR_LEN>::step_1(
        &mut prover_state,
        &memory,
        traces
            .iter()
            .flat_map(|(table, trace)| table.vector_lookup_index_columns(trace))
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| vec![trace.n_rows_non_padded_maxed(); table.num_vector_lookups()])
            .collect(),
        traces
            .keys()
            .flat_map(|table| table.vector_lookup_default_indexes())
            .collect(),
        traces
            .iter()
            .flat_map(|(table, trace)| table.vector_lookup_values_columns(trace))
            .collect(),
        {
            let mut statements = vec![];
            for (table, _) in &traces {
                if table.identifier() == Table::poseidon24() {
                    statements.extend(poseidon_24_vectorized_lookup_statements(&p24_gkr)); // special case
                    continue;
                }
                statements.extend(table.vectorized_lookups_statements(&air_points[table], &evals_f[table]));
            }
            statements
        },
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

    let mut normal_lookup_statements = normal_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let vectorized_lookup_statements = vectorized_lookup_into_memory.step_2(&mut prover_state, non_zero_memory_size);

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &traces[&Table::execution()].base[COL_INDEX_PC],
        bytecode_lookup_claim_1.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward,
        Some(bytecode.instructions.len()),
    );

    let memory_statements = vec![
        normal_lookup_statements.on_table.clone(),
        vectorized_lookup_statements.on_table.clone(),
    ];

    let mut final_statements: BTreeMap<Table, Vec<Vec<Evaluation<EF>>>> = Default::default();
    for (table, _) in &traces {
        final_statements.insert(
            *table,
            table.committed_statements_prover(
                &mut prover_state,
                &air_points[table],
                &evals_f[table],
                commitmenent_extension_helper.get(table),
                &mut normal_lookup_statements.on_indexes_f,
                &mut normal_lookup_statements.on_indexes_ef,
            ),
        );
    }
    assert!(normal_lookup_statements.on_indexes_f.is_empty());
    assert!(normal_lookup_statements.on_indexes_ef.is_empty());

    let p16_gkr = prove_poseidon_gkr(
        &mut prover_state,
        &p16_witness,
        air_points[&Table::poseidon16_core()].0.clone(),
        UNIVARIATE_SKIPS,
        &p16_gkr_layers,
    );
    assert_eq!(&p16_gkr.output_statements.point, &air_points[&Table::poseidon16_core()]);
    assert_eq!(
        &p16_gkr.output_statements.values,
        &evals_f[&Table::poseidon16_core()][POSEIDON_16_CORE_COL_OUTPUT_START..][..16]
    );
    // TODO p16_gkr.input / p16_gkr.compression

    {
        let mut cursor = 0;
        for (table, _) in &traces {
            for (statement, lookup) in vectorized_lookup_statements.on_indexes[cursor..]
                .iter()
                .zip(table.vector_lookups())
            {
                final_statements.get_mut(table).unwrap()[lookup.index].extend(statement.clone());
            }
            cursor += table.num_vector_lookups();
        }
    }

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(traces[&Table::execution()].log_padded());

    final_statements.get_mut(&Table::execution()).unwrap()[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)]
        .extend(vec![
            bytecode_logup_star_statements.on_indexes.clone(),
            initial_pc_statement,
            final_pc_statement,
        ]);
    let statements_p16_core = final_statements.get_mut(&Table::poseidon16_core()).unwrap();
    for (stmts, gkr_value) in statements_p16_core[POSEIDON_16_CORE_COL_INPUT_START..][..16]
        .iter_mut()
        .zip(&p16_gkr.input_statements.values)
    {
        stmts.push(Evaluation::new(p16_gkr.input_statements.point.clone(), *gkr_value));
    }
    statements_p16_core[POSEIDON_16_CORE_COL_COMPRESSION].push(p16_gkr.on_compression_selector.unwrap());

    // First Opening
    let mut all_base_statements = [
        vec![memory_statements],
        encapsulate_vec(p16_gkr.cubes_statements.split()),
        encapsulate_vec(p24_gkr.cubes_statements.split()),
    ]
    .concat();
    all_base_statements.extend(final_statements.into_values().flatten());

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

    (prover_state.into_proof(), exec_summary)
}

fn prove_bus_and_air(
    prover_state: &mut multilinear_toolkit::prelude::FSProver<EF, impl FSChallenger<EF>>,
    t: &Table,
    trace: &TableTrace,
    bus_challenge: EF,
    fingerprint_challenge: EF,
) -> (EF, MultilinearPoint<EF>, Vec<EF>, Vec<EF>) {
    let n_buses = t.buses().len();
    let n_buses_padded = n_buses.next_power_of_two();
    let log_n_buses = log2_ceil_usize(n_buses);
    let n_rows = trace.n_rows_padded();
    let log_n_rows = trace.log_padded();

    assert!(n_buses > 0, "Table {} has no buses", t.name());

    let mut numerators = F::zero_vec(n_buses_padded * n_rows);
    for (bus, numerators_chunk) in t.buses().iter().zip(numerators.chunks_mut(n_rows)) {
        match bus.selector {
            BusSelector::Column(selector_col) => {
                assert!(selector_col < trace.base.len());
                trace.base[selector_col]
                    .par_iter()
                    .zip(numerators_chunk)
                    .for_each(|(&selector, v)| {
                        *v = match bus.direction {
                            BusDirection::Pull => -selector,
                            BusDirection::Push => selector,
                        }
                    });
            }
            BusSelector::ConstantOne => {
                numerators_chunk.par_iter_mut().for_each(|v| {
                    *v = match bus.direction {
                        BusDirection::Pull => F::NEG_ONE,
                        BusDirection::Push => F::ONE,
                    }
                });
            }
        }
    }

    let mut denominators = unsafe { uninitialized_vec(n_buses_padded * n_rows) };
    for (bus, denomniators_chunk) in t.buses().iter().zip(denominators.chunks_exact_mut(n_rows)) {
        denomniators_chunk.par_iter_mut().enumerate().for_each(|(i, v)| {
            *v = bus_challenge
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
                );
        });
    }
    denominators[n_rows * n_buses..]
        .par_iter_mut()
        .for_each(|v| *v = EF::ONE);

    // TODO avoid embedding !!
    let numerators_embedded = numerators.par_iter().copied().map(EF::from).collect::<Vec<_>>();

    // TODO avoid reallocation due to packing (pack directly when constructing)
    let numerators_packed = pack_extension(&numerators_embedded);
    let denominators_packed = pack_extension(&denominators);
    let (mut quotient, bus_point_global, numerator_value_global, denominator_value_global) =
        prove_gkr_quotient::<_, TWO_POW_UNIVARIATE_SKIPS>(
            prover_state,
            &MleGroupRef::ExtensionPacked(vec![&numerators_packed, &denominators_packed]),
        );

    let (bus_point, bus_selector_values, bus_data_values) = if n_buses == 1 {
        // easy case
        (
            bus_point_global,
            vec![numerator_value_global],
            vec![denominator_value_global],
        )
    } else {
        let uni_selectors = univariate_selectors::<F>(UNIVARIATE_SKIPS);

        let sub_numerators_evals = numerators
            .par_chunks_exact(1 << (log_n_rows - UNIVARIATE_SKIPS))
            .take(n_buses << UNIVARIATE_SKIPS)
            .map(|chunk| chunk.evaluate(&MultilinearPoint(bus_point_global[1 + log_n_buses..].to_vec())))
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&sub_numerators_evals);
        // sanity check:
        assert_eq!(
            numerator_value_global,
            evaluate_univariate_multilinear::<_, _, _, false>(
                &padd_with_zero_to_next_power_of_two(&sub_numerators_evals),
                &bus_point_global[..1 + log_n_buses],
                &uni_selectors,
                None
            ),
        );

        let sub_denominators_evals = denominators
            .par_chunks_exact(1 << (log_n_rows - UNIVARIATE_SKIPS))
            .take(n_buses << UNIVARIATE_SKIPS)
            .map(|chunk| chunk.evaluate(&MultilinearPoint(bus_point_global[1 + log_n_buses..].to_vec())))
            .collect::<Vec<_>>();
        prover_state.add_extension_scalars(&sub_denominators_evals);
        // sanity check:
        assert_eq!(
            denominator_value_global,
            evaluate_univariate_multilinear::<_, _, _, false>(
                &padd_to_next_power_of_two(&sub_denominators_evals, EF::ONE),
                &bus_point_global[..1 + log_n_buses],
                &uni_selectors,
                None
            ),
        );

        let epsilon = prover_state.sample();
        let bus_point = MultilinearPoint([vec![epsilon], bus_point_global[1 + log_n_buses..].to_vec()].concat());

        let bus_selector_values = sub_numerators_evals
            .chunks_exact(1 << UNIVARIATE_SKIPS)
            .map(|chunk| evaluate_univariate_multilinear::<_, _, _, false>(chunk, &[epsilon], &uni_selectors, None))
            .collect();
        let bus_data_values = sub_denominators_evals
            .chunks_exact(1 << UNIVARIATE_SKIPS)
            .map(|chunk| evaluate_univariate_multilinear::<_, _, _, false>(chunk, &[epsilon], &uni_selectors, None))
            .collect();

        (bus_point, bus_selector_values, bus_data_values)
    };

    let bus_beta = prover_state.sample();

    let bus_final_values = bus_selector_values
        .iter()
        .zip_eq(&bus_data_values)
        .zip_eq(&t.buses())
        .map(|((&bus_selector_value, &bus_data_value), bus)| {
            bus_selector_value
                * match bus.direction {
                    BusDirection::Pull => EF::NEG_ONE,
                    BusDirection::Push => EF::ONE,
                }
                + bus_beta * (bus_data_value - bus_challenge)
        })
        .collect::<Vec<_>>();

    let bus_virtual_statement = MultiEvaluation::new(bus_point, bus_final_values);

    for bus in t.buses() {
        quotient -= bus.padding_contribution(t, trace.padding_len(), bus_challenge, fingerprint_challenge);
    }

    let extra_data = ExtraDataForBuses {
        fingerprint_challenge_powers: fingerprint_challenge.powers().collect_n(max_bus_width()),
        fingerprint_challenge_powers_packed: EFPacking::<EF>::from(fingerprint_challenge)
            .powers()
            .collect_n(max_bus_width()),
        bus_beta,
        bus_beta_packed: EFPacking::<EF>::from(bus_beta),
        alpha_powers: vec![], // filled later
    };

    let (air_point, evals_f, evals_ef) = info_span!("Table AIR proof", table = t.name()).in_scope(|| {
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

    (quotient, air_point, evals_f, evals_ef)
}
