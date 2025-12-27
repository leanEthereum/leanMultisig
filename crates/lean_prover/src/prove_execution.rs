use std::collections::BTreeMap;

use crate::common::*;
use crate::*;
use air::prove_air;
use lean_vm::*;
use multilinear_toolkit::prelude::*;

use p3_util::log2_ceil_usize;
use sub_protocols::*;
use tracing::info_span;
use utils::{build_prover_state, padd_with_zero_to_next_power_of_two};
use whir_p3::WhirConfig;
use xmss::Poseidon16History;

#[derive(Debug)]
pub struct ExecutionProof {
    pub proof: Vec<F>,
    pub proof_size_fe: usize,
    pub exec_summary: String,
    pub first_whir_n_vars: usize,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    (public_input, private_input): (&[F], &[F]),
    poseidons_16_precomputed: &Poseidon16History,
    params: &SnarkParams,
    vm_profiler: bool,
) -> ExecutionProof {
    let mut exec_summary = String::new();
    let ExecutionTrace {
        traces,
        public_memory_size,
        non_zero_memory_size: _, // TODO use the information of the ending zeros for speedup
        mut memory,              // padded with zeros to next power of two
    } = info_span!("Witness generation").in_scope(|| {
        let mut execution_result = info_span!("Executing bytecode").in_scope(|| {
            execute_bytecode(
                bytecode,
                (public_input, private_input),
                vm_profiler,
                poseidons_16_precomputed,
            )
        });
        exec_summary = std::mem::take(&mut execution_result.summary);
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    if memory.len() < 1 << MIN_LOG_MEMORY_SIZE {
        memory.resize(1 << MIN_LOG_MEMORY_SIZE, F::ZERO);
    }

    let mut prover_state = build_prover_state();
    prover_state.add_base_scalars(
        &[
            vec![log2_strict_usize(memory.len())],
            traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
        ]
        .concat()
        .into_iter()
        .map(F::from_usize)
        .collect::<Vec<_>>(),
    );

    // TODO parrallelize
    let mut acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups_f() {
                for i in &trace.base[lookup.index] {
                    for j in 0..lookup.values.len() {
                        acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
            for lookup in table.lookups_ef() {
                for i in &trace.base[lookup.index] {
                    for j in 0..DIMENSION {
                        acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    // 1st Commitment
    let packed_pcs_witness_base = packed_pcs_commit(&mut prover_state, &params.first_whir, &memory, &acc, &traces);
    let first_whir_n_vars = packed_pcs_witness_base.packed_polynomial.by_ref().n_vars();

    // logup (GKR)
    let logup_c = prover_state.sample();
    prover_state.duplexing();
    let logup_alpha = prover_state.sample();
    prover_state.duplexing();

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        logup_alpha,
        &memory,
        &acc,
        &traces,
        UNIVARIATE_SKIPS,
    );

    let (mut air_points, mut evals_f, mut evals_ef) = (BTreeMap::new(), BTreeMap::new(), BTreeMap::new());
    for (table, trace) in traces.iter() {
        let (this_air_point, this_evals_f, this_evals_ef) = prove_bus_and_air(
            &mut prover_state,
            table,
            trace,
            logup_c,
            logup_alpha,
            &logup_statements.bus_numerators[table],
            &logup_statements.bus_denominators[table],
        );
        air_points.insert(*table, this_air_point);
        evals_f.insert(*table, this_evals_f);
        evals_ef.insert(*table, this_evals_ef);
    }

    let bytecode_compression_challenges =
        MultilinearPoint(prover_state.sample_vec(log2_ceil_usize(N_INSTRUCTION_COLUMNS)));

    let folded_bytecode = fold_bytecode(bytecode, &bytecode_compression_challenges);

    let bytecode_lookup_claim = Evaluation::new(
        air_points[&Table::execution()].clone(),
        padd_with_zero_to_next_power_of_two(
            &evals_f[&Table::execution()][N_COMMITTED_EXEC_COLUMNS..][..N_INSTRUCTION_COLUMNS],
        )
        .evaluate(&bytecode_compression_challenges),
    );
    let bytecode_poly_eq_point = eval_eq(&air_points[&Table::execution()]);
    let bytecode_pushforward = MleOwned::Extension(compute_pushforward(
        &traces[&Table::execution()].base[COL_INDEX_PC],
        folded_bytecode.len(),
        &bytecode_poly_eq_point,
    ));

    let bytecode_pushforward_commitment =
        WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len()))
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

    let memory_statements = vec![logup_statements.on_memory, public_memory_statement];
    let acc_statements = vec![logup_statements.on_acc];

    let mut commited_statements_f: BTreeMap<Table, Vec<Vec<Evaluation<EF>>>> = Default::default();
    for table in traces.keys() {
        commited_statements_f.insert(
            *table,
            table.committed_statements_f(&air_points[table], &evals_f[table], &logup_statements.columns_f[table]),
        );
    }

    let mut commited_statements_ef: BTreeMap<Table, Vec<Vec<MultiEvaluation<EF>>>> = Default::default();
    for table in traces.keys() {
        commited_statements_ef.insert(
            *table,
            table.committed_statements_prover_ef(
                &mut prover_state,
                &air_points[table],
                &evals_ef[table],
                &traces[table],
                &logup_statements.columns_ef[table],
            ),
        );
    }

    let (initial_pc_statement, final_pc_statement) =
        initial_and_final_pc_conditions(traces[&Table::execution()].log_n_rows);

    commited_statements_f.get_mut(&Table::execution()).unwrap()[COL_INDEX_PC].extend(vec![
        bytecode_logup_star_statements.on_indexes.clone(),
        initial_pc_statement,
        final_pc_statement,
    ]);

    let table_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let global_statements_base = packed_pcs_global_statements(
        packed_pcs_witness_base.packed_n_vars,
        &table_heights,
        &memory_statements,
        &acc_statements,
        &commited_statements_f,
        &commited_statements_ef,
    );

    WhirConfig::new(
        &params.first_whir,
        packed_pcs_witness_base.packed_polynomial.by_ref().n_vars(),
    )
    .prove(
        &mut prover_state,
        global_statements_base,
        packed_pcs_witness_base.inner_witness,
        &packed_pcs_witness_base.packed_polynomial.by_ref(),
    );

    WhirConfig::new(&params.second_whir, log2_ceil_usize(bytecode.instructions.len())).prove(
        &mut prover_state,
        bytecode_logup_star_statements.on_pushforward,
        bytecode_pushforward_commitment,
        &bytecode_pushforward.by_ref(),
    );
    let proof_size_fe = prover_state.proof_size_fe();
    ExecutionProof {
        proof: prover_state.into_proof(),
        proof_size_fe,
        exec_summary,
        first_whir_n_vars,
    }
}

fn prove_bus_and_air(
    prover_state: &mut impl FSProver<EF>,
    table: &Table,
    trace: &TableTrace,
    logup_c: EF,
    logup_alpha: EF,
    bus_numerator_statement: &Evaluation<EF>,
    bus_denominator_statement: &Evaluation<EF>,
) -> (MultilinearPoint<EF>, Vec<EF>, Vec<EF>) {
    let bus_point = bus_numerator_statement.point.clone();
    assert_eq!(bus_point, bus_denominator_statement.point,);

    let bus_beta = prover_state.sample();
    prover_state.duplexing();

    let bus_final_value = bus_numerator_statement.value
        * match table.bus().direction {
            BusDirection::Pull => EF::NEG_ONE,
            BusDirection::Push => EF::ONE,
        }
        + bus_beta * (bus_denominator_statement.value - logup_c);

    let bus_virtual_statement = Evaluation::new(bus_point, bus_final_value);

    let extra_data = ExtraDataForBuses {
        logup_alpha_powers: logup_alpha.powers().collect_n(max_bus_width()),
        logup_alpha_powers_packed: EFPacking::<EF>::from(logup_alpha).powers().collect_n(max_bus_width()),
        bus_beta,
        bus_beta_packed: EFPacking::<EF>::from(bus_beta),
        alpha_powers: vec![], // filled later
    };

    let (air_point, evals_f, evals_ef) = info_span!("AIR proof", table = table.name()).in_scope(|| {
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
        delegate_to_inner!(table => prove_air_for_table)
    });

    (air_point, evals_f, evals_ef)
}
