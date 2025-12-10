use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::prove_air;
use itertools::Itertools;
use lean_vm::*;
use lookup::{compute_pushforward, prove_logup_star};
use multilinear_toolkit::prelude::*;

use p3_util::log2_ceil_usize;
use sub_protocols::*;
use tracing::info_span;
use utils::{build_prover_state, padd_with_zero_to_next_power_of_two};
use whir_p3::WhirConfig;
use xmss::Poseidon16History;

pub fn prove_execution(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    no_vec_runtime_memory: usize, // size of the "non-vectorized" runtime memory
    vm_profiler: bool,
    poseidons_16_precomputed: &Poseidon16History,
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
                poseidons_16_precomputed,
            )
        });
        exec_summary = std::mem::take(&mut execution_result.summary);
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    if memory.len() < 1 << MIN_LOG_MEMORY_SIZE {
        memory.resize(1 << MIN_LOG_MEMORY_SIZE, F::ZERO);
        non_zero_memory_size = 1 << MIN_LOG_MEMORY_SIZE;
    }

    let mut prover_state = build_prover_state::<EF>(false);
    prover_state.add_base_scalars(
        &[
            vec![non_zero_memory_size],
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
            trace.n_rows_non_padded() > 0 || table == &Table::execution() || table == &Table::poseidon16()
        })
        .collect();

    // TODO parrallelize
    let mut acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.normal_lookups_f() {
                for i in &trace.base[lookup.index] {
                    acc[i.to_usize()] += F::ONE;
                }
            }
            for lookup in table.normal_lookups_ef() {
                for i in &trace.base[lookup.index] {
                    for j in 0..DIMENSION {
                        acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
            for lookup in table.vector_lookups() {
                for i in &trace.base[lookup.index] {
                    for j in 0..VECTOR_LEN {
                        acc[i.to_usize() * VECTOR_LEN + j] += F::ONE;
                    }
                }
            }
        }
    });

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
        non_zero_memory_size,
        &traces.iter().map(|(table, trace)| (*table, trace.height)).collect(),
    );

    let mut base_pols = vec![memory.as_slice(), acc.as_slice()];
    for (table, trace) in &traces {
        base_pols.extend(table.committed_columns(trace, commitmenent_extension_helper.get(table)));
    }

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(
        &whir_config_builder_a(),
        &base_pols,
        &base_dims,
        &mut prover_state,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
    );

    let bus_challenge = prover_state.sample();
    let fingerprint_challenge = prover_state.sample();

    let mut bus_numerators = vec![];
    let mut bus_denominators = vec![];
    for (table, trace) in &traces {
        for bus in table.buses() {
            let numerator = trace.base[bus.selector]
                .par_iter()
                .map(|&selector| match bus.direction {
                    BusDirection::Pull => -selector,
                    BusDirection::Push => selector,
                })
                .collect::<Vec<_>>();
            let denominator = (0..trace.n_rows_padded())
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

            bus_numerators.push(numerator);
            bus_denominators.push(denominator);
        }
    }

    let mut lookup_into_memory = CustomLookupProver::run::<EF, DIMENSION, VECTOR_LEN>(
        &mut prover_state,
        &memory,
        &acc,
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
            .flat_map(|(table, trace)| table.vector_lookup_index_columns(trace))
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
            .iter()
            .flat_map(|(table, trace)| table.vector_lookup_values_columns(trace))
            .collect(),
        collect_refs(&bus_numerators),
        collect_refs(&bus_denominators),
        UNIVARIATE_SKIPS,
    );

    let mut air_points: BTreeMap<Table, MultilinearPoint<EF>> = Default::default();
    let mut evals_f: BTreeMap<Table, Vec<EF>> = Default::default();
    let mut evals_ef: BTreeMap<Table, Vec<EF>> = Default::default();

    let mut bus_offset = 0;
    for (table, trace) in &traces {
        let (this_air_point, this_evals_f, this_evals_ef) = prove_bus_and_air(
            &mut prover_state,
            table,
            trace,
            bus_challenge,
            fingerprint_challenge,
            &lookup_into_memory.on_bus_denominators[bus_offset..][..table.buses().len()],
            &lookup_into_memory.on_bus_numerators[bus_offset..][..table.buses().len()],
        );
        air_points.insert(*table, this_air_point);
        evals_f.insert(*table, this_evals_f);
        evals_ef.insert(*table, this_evals_ef);
        bus_offset += table.buses().len();
    }
    assert_eq_many!(
        bus_offset,
        lookup_into_memory.on_bus_numerators.len(),
        lookup_into_memory.on_bus_denominators.len()
    );

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(&evals_f[&Table::execution()][..N_INSTRUCTION_COLUMNS])
            .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_poly_eq_point = eval_eq(&air_points[&Table::execution()]);
    let bytecode_pushforward = MleOwned::Extension(compute_pushforward(
        &traces[&Table::execution()].base[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    ));

    let bytecode_pushforward_commitment =
        WhirConfig::new(whir_config_builder_b(), log2_ceil_usize(bytecode.instructions.len()))
            .commit(&mut prover_state, &bytecode_pushforward);

    let bytecode_logup_star_statements = prove_logup_star(
        &mut prover_state,
        &MleRef::Extension(&folded_bytecode),
        &traces[&Table::execution()].base[COL_INDEX_PC],
        bytecode_lookup_claim.value,
        &bytecode_poly_eq_point,
        &bytecode_pushforward.by_ref(),
        Some(bytecode.instructions.len()),
    );

    let mut public_memory_random_point =
        MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);
    public_memory_random_point
        .0
        .splice(0..0, EF::zero_vec(log2_strict_usize(memory.len() / public_memory_size)));
    let public_memory_statement = Evaluation::new(public_memory_random_point, public_memory_eval);

    let memory_statements = vec![lookup_into_memory.on_table, public_memory_statement];
    let acc_statements = vec![lookup_into_memory.on_acc];

    let mut final_statements: BTreeMap<Table, Vec<Vec<Evaluation<EF>>>> = Default::default();
    for table in traces.keys() {
        final_statements.insert(
            *table,
            table.committed_statements_prover(
                &mut prover_state,
                &air_points[table],
                &evals_f[table],
                commitmenent_extension_helper.get(table),
                &mut lookup_into_memory.on_indexes_f,
                &mut lookup_into_memory.on_indexes_ef,
                &mut lookup_into_memory.on_indexes_vec,
                &mut lookup_into_memory.on_values_f,
                &mut lookup_into_memory.on_values_ef,
                &mut lookup_into_memory.on_values_vec,
            ),
        );
    }
    assert!(lookup_into_memory.on_indexes_f.is_empty());
    assert!(lookup_into_memory.on_indexes_ef.is_empty());
    assert!(lookup_into_memory.on_indexes_vec.is_empty());
    assert!(lookup_into_memory.on_values_f.is_empty());
    assert!(lookup_into_memory.on_values_ef.is_empty());
    assert!(lookup_into_memory.on_values_vec.is_empty());

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(traces[&Table::execution()].log_padded());

    final_statements.get_mut(&Table::execution()).unwrap()[ExecutionTable.find_committed_column_index_f(COL_INDEX_PC)]
        .extend(vec![
            bytecode_logup_star_statements.on_indexes.clone(),
            initial_pc_statement,
            final_pc_statement,
        ]);

    // First Opening
    let mut all_base_statements = vec![memory_statements, acc_statements];
    all_base_statements.extend(final_statements.into_values().flatten());

    let global_statements_base = packed_pcs_global_statements_for_prover(
        &base_pols,
        &base_dims,
        LOG_SMALLEST_DECOMPOSITION_CHUNK,
        &all_base_statements,
        &mut prover_state,
    );

    WhirConfig::new(
        whir_config_builder_a(),
        packed_pcs_witness_base.packed_polynomial.by_ref().n_vars(),
    )
    .prove(
        &mut prover_state,
        global_statements_base,
        packed_pcs_witness_base.inner_witness,
        &packed_pcs_witness_base.packed_polynomial.by_ref(),
    );

    WhirConfig::new(whir_config_builder_b(), log2_ceil_usize(bytecode.instructions.len())).prove(
        &mut prover_state,
        bytecode_logup_star_statements.on_pushforward,
        bytecode_pushforward_commitment,
        &bytecode_pushforward.by_ref(),
    );

    (prover_state.into_proof(), exec_summary)
}

fn prove_bus_and_air(
    prover_state: &mut multilinear_toolkit::prelude::FSProver<EF, impl FSChallenger<EF>>,
    t: &Table,
    trace: &TableTrace,
    bus_challenge: EF,
    fingerprint_challenge: EF,
    bus_numerator_statements: &[Evaluation<EF>],
    bus_denominator_statements: &[Evaluation<EF>],
) -> (MultilinearPoint<EF>, Vec<EF>, Vec<EF>) {
    assert_eq!(t.buses().len(), bus_numerator_statements.len());
    let bus_point = bus_numerator_statements[0].point.clone();
    assert!(t.buses().iter().all(|_| bus_numerator_statements[0].point == bus_point));
    assert!(
        t.buses()
            .iter()
            .all(|_| bus_denominator_statements[0].point == bus_point)
    );

    let bus_beta = prover_state.sample();

    let bus_final_values = bus_numerator_statements
        .iter()
        .zip_eq(bus_denominator_statements)
        .zip_eq(t.buses())
        .map(|((bus_selector_statement, bus_data_statement), bus)| {
            bus_selector_statement.value
                * match bus.direction {
                    BusDirection::Pull => EF::NEG_ONE,
                    BusDirection::Push => EF::ONE,
                }
                + bus_beta * (bus_data_statement.value - bus_challenge)
        })
        .collect::<Vec<_>>();

    let bus_virtual_statement = MultiEvaluation::new(bus_point, bus_final_values);

    let extra_data = ExtraDataForBuses {
        fingerprint_challenge_powers: fingerprint_challenge.powers().collect_n(max_bus_width()),
        fingerprint_challenge_powers_packed: EFPacking::<EF>::from(fingerprint_challenge)
            .powers()
            .collect_n(max_bus_width()),
        bus_beta,
        bus_beta_packed: EFPacking::<EF>::from(bus_beta),
        alpha_powers: vec![], // filled later
    };

    let (air_point, evals_f, evals_ef) = info_span!("AIR proof", table = t.name()).in_scope(|| {
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

    (air_point, evals_f, evals_ef)
}
