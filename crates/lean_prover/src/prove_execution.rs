use std::collections::BTreeMap;

use crate::*;
use backend::merkle::Sha256Digest;
use lean_vm::*;

use serde::{Deserialize, Serialize};
use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, build_prover_state_sha2, from_end};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    pub proof2: Proof<F, Sha256Digest>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let ExecutionTrace {
        traces,
        public_memory_size,
        mut memory, // padded with zeros to next power of two
        metadata,
    } = info_span!("Witness generation").in_scope(|| -> Result<_, ProverError> {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| try_execute_bytecode(bytecode, public_input, witness, vm_profiler))?;
        Ok(info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result)))
    })?;

    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size
    // (required by the stacked polynomial ordering)
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    let mut prover_state = build_prover_state();
    let mut prover_state2 = build_prover_state_sha2();
    prover_state.observe_scalars(public_input);
    prover_state2.observe_scalars(public_input);
    let bytecode_hash_with_domain_sep = poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP);
    prover_state.observe_scalars(&bytecode_hash_with_domain_sep);
    prover_state2.observe_scalars(&bytecode_hash_with_domain_sep);
    let execution_metadata_scalars = [
        vec![
            whir_config.starting_log_inv_rate,
            log2_strict_usize(memory.len()),
            public_input.len(),
        ],
        traces.values().map(|t| t.log_n_rows).collect::<Vec<_>>(),
    ]
    .concat()
    .into_iter()
    .map(F::from_usize)
    .collect::<Vec<_>>();
    prover_state.add_base_scalars(&execution_metadata_scalars);
    prover_state2.add_base_scalars(&execution_metadata_scalars);
    for (table, table_trace) in &traces {
        let log_n_rows = table_trace.log_n_rows;
        assert!(log_n_rows >= MIN_LOG_N_ROWS_PER_TABLE, "missing padding");
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return Err(TooBigTableError {
                table_name: table.name(),
                log_n_rows,
                log_limit,
            }
            .into());
        }
    }

    let mut table_log = String::new();
    for (table, trace) in &traces {
        table_log.push_str(&format!(
            "{}: 2^{} * (1 + {:.2}) rows | ",
            table.name(),
            trace.log_n_rows - 1,
            (trace.non_padded_n_rows as f64) / (1 << (trace.log_n_rows - 1)) as f64 - 1.0
        ));
    }
    table_log = table_log.trim_end_matches(" | ").to_string();
    tracing::info!("Trace tables sizes: {}", table_log.magenta());

    // TODO parrallelize
    let mut memory_acc = F::zero_vec(memory.len());
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups() {
                for i in &trace.columns[lookup.index] {
                    for j in 0..lookup.values.len() {
                        memory_acc[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    // // TODO parrallelize
    let mut bytecode_acc = F::zero_vec(bytecode.padded_size());
    info_span!("Building bytecode access count").in_scope(|| {
        for pc in traces[&Table::execution()].columns[COL_PC].iter() {
            bytecode_acc[pc.to_usize()] += F::ONE;
        }
    });

    // 1st Commitment
    let stacked_pcs_witness = stack_polynomials_and_commit(
        &mut prover_state,
        &mut prover_state2,
        whir_config,
        &memory,
        &memory_acc,
        &bytecode_acc,
        &traces,
    );

    // logup (GKR)
    let logup_c = prover_state.sample();
    let logup_alphas = prover_state.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas_eq_poly,
        &memory,
        &memory_acc,
        &bytecode.instructions_multilinear,
        &bytecode_acc,
        &traces,
    );
    let logup_c2 = prover_state2.sample();
    let logup_alphas2 = prover_state2.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
    let logup_alphas_eq_poly2 = eval_eq(&logup_alphas2);

    let logup_statements2 = prove_generic_logup(
        &mut prover_state2,
        logup_c2,
        &logup_alphas_eq_poly2,
        &memory,
        &memory_acc,
        &bytecode.instructions_multilinear,
        &bytecode_acc,
        &traces,
    );
    let gkr_point = &logup_statements.gkr_point;
    let gkr_point2 = &logup_statements2.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
    let mut committed_statements2: CommittedStatements = Default::default();
    for table in ALL_TABLES {
        let log_n_rows = traces[&table].log_n_rows;
        committed_statements.insert(
            table,
            vec![(
                MultilinearPoint(from_end(gkr_point, log_n_rows).to_vec()),
                logup_statements.columns_values[&table].clone(),
                BTreeMap::new(),
            )],
        );
        committed_statements2.insert(
            table,
            vec![(
                MultilinearPoint(from_end(gkr_point2, log_n_rows).to_vec()),
                logup_statements2.columns_values[&table].clone(),
                BTreeMap::new(),
            )],
        );
    }

    let bus_beta = prover_state.sample();
    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);
    let air_eta: EF = prover_state.sample();
    let bus_beta2 = prover_state2.sample();
    let air_alpha2 = prover_state2.sample();
    let air_alpha_powers2: Vec<EF> = air_alpha2.powers().collect_n(max_air_constraints() + 1);
    let air_eta2: EF = prover_state2.sample();

    let tables_log_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_sorted = sort_tables_by_height(&tables_log_heights);

    let column_refs: Vec<Vec<&[F]>> = tables_sorted
        .iter()
        .map(|(table, _)| {
            traces[table].columns[..table.n_columns()]
                .iter()
                .map(Vec::as_slice)
                .collect()
        })
        .collect();
    let _span = info_span!("Computing shifted columns for AIR sumcheck").entered();
    let shifted_rows: Vec<Vec<Vec<F>>> = tables_sorted
        .par_iter()
        .zip(&column_refs)
        .map(|((table, _), cols)| compute_shifted_columns(&table.down_column_indexes(), cols))
        .collect();
    std::mem::drop(_span);
    let mut sessions = Vec::with_capacity(tables_sorted.len());
    let mut sessions2 = Vec::with_capacity(tables_sorted.len());
    for (idx, (table, log_n_rows)) in tables_sorted.iter().enumerate() {
        let bus_numerator_value = logup_statements.bus_numerators_values[table];
        let bus_denominator_value = logup_statements.bus_denominators_values[table];
        let bus_final_value = bus_numerator_value
            * match table.bus().direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            }
            + bus_beta * (bus_denominator_value - logup_c);

        let eq_suffix = from_end(gkr_point, *log_n_rows).to_vec();

        let extra_data = ExtraDataForBuses::new(logup_alphas_eq_poly.clone(), bus_beta, air_alpha_powers.clone());

        let mut up_down: Vec<&[PF<EF>]> = column_refs[idx].to_vec();
        up_down.extend(shifted_rows[idx].iter().map(Vec::as_slice));
        let packed = MleGroupRef::<EF>::Base(up_down).pack();

        let non_padded = traces[table].non_padded_n_rows;

        macro_rules! make_session {
            ($t:expr) => {{
                let session = AirSumcheckSession::new(packed, eq_suffix, bus_final_value, *$t, extra_data, non_padded);
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        sessions.push(delegate_to_inner!(table => make_session));

        let bus_numerator_value2 = logup_statements2.bus_numerators_values[table];
        let bus_denominator_value2 = logup_statements2.bus_denominators_values[table];
        let bus_final_value2 = bus_numerator_value2
            * match table.bus().direction {
                BusDirection::Pull => EF::NEG_ONE,
                BusDirection::Push => EF::ONE,
            }
            + bus_beta2 * (bus_denominator_value2 - logup_c2);

        let eq_suffix2 = from_end(gkr_point2, *log_n_rows).to_vec();

        let extra_data2 = ExtraDataForBuses::new(logup_alphas_eq_poly2.clone(), bus_beta2, air_alpha_powers2.clone());

        let mut up_down2: Vec<&[PF<EF>]> = column_refs[idx].to_vec();
        up_down2.extend(shifted_rows[idx].iter().map(Vec::as_slice));
        let packed2 = MleGroupRef::<EF>::Base(up_down2).pack();

        macro_rules! make_session2 {
            ($t:expr) => {{
                let session = AirSumcheckSession::new(
                    packed2,
                    eq_suffix2,
                    bus_final_value2,
                    *$t,
                    extra_data2,
                    non_padded,
                );
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        sessions2.push(delegate_to_inner!(table => make_session2));
    }

    let sumcheck_air_point = info_span!("batched AIR sumcheck")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta));
    let sumcheck_air_point2 = info_span!("batched AIR sumcheck sha2")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state2, &mut sessions2, air_eta2));

    for (idx, (table, _)) in tables_sorted.iter().enumerate() {
        let col_evals = sessions[idx].final_column_evals();
        prover_state.add_extension_scalars(&col_evals);

        let natural_ordering_point =
            natural_ordering_point_for_session(&sumcheck_air_point.0, traces[table].log_n_rows);
        macro_rules! split {
            ($t:expr) => {{ columns_evals_up_and_down($t, &col_evals, &natural_ordering_point) }};
        }
        let claim = delegate_to_inner!(table => split);
        committed_statements.get_mut(table).unwrap().push(claim);

        let col_evals2 = sessions2[idx].final_column_evals();
        prover_state2.add_extension_scalars(&col_evals2);

        let natural_ordering_point2 =
            natural_ordering_point_for_session(&sumcheck_air_point2.0, traces[table].log_n_rows);
        macro_rules! split2 {
            ($t:expr) => {{ columns_evals_up_and_down($t, &col_evals2, &natural_ordering_point2) }};
        }
        let claim2 = delegate_to_inner!(table => split2);
        committed_statements2.get_mut(table).unwrap().push(claim2);
    }

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);
    let public_memory_random_point2 = MultilinearPoint(prover_state2.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval2 = (&memory[..public_memory_size]).evaluate(&public_memory_random_point2);

    let previous_statements = vec![
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            logup_statements.memory_and_acc_point,
            vec![
                SparseValue::new(0, logup_statements.value_memory),
                SparseValue::new(1, logup_statements.value_memory_acc),
            ],
        ),
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            public_memory_random_point,
            vec![SparseValue::new(0, public_memory_eval)],
        ),
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            logup_statements.bytecode_and_acc_point,
            vec![SparseValue::new(
                (2 * memory.len()) >> bytecode.log_size(),
                logup_statements.value_bytecode_acc,
            )],
        ),
    ];
    let previous_statements2 = vec![
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            logup_statements2.memory_and_acc_point,
            vec![
                SparseValue::new(0, logup_statements2.value_memory),
                SparseValue::new(1, logup_statements2.value_memory_acc),
            ],
        ),
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            public_memory_random_point2,
            vec![SparseValue::new(0, public_memory_eval2)],
        ),
        SparseStatement::new(
            stacked_pcs_witness.stacked_n_vars,
            logup_statements2.bytecode_and_acc_point,
            vec![SparseValue::new(
                (2 * memory.len()) >> bytecode.log_size(),
                logup_statements2.value_bytecode_acc,
            )],
        ),
    ];

    let global_statements_base = stacked_pcs_global_statements(
        stacked_pcs_witness.stacked_n_vars,
        log2_strict_usize(memory.len()),
        bytecode.log_size(),
        previous_statements,
        &tables_log_heights,
        &committed_statements,
    );
    let global_statements_base2 = stacked_pcs_global_statements(
        stacked_pcs_witness.stacked_n_vars,
        log2_strict_usize(memory.len()),
        bytecode.log_size(),
        previous_statements2,
        &tables_log_heights,
        &committed_statements2,
    );

    WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()).prove(
        &mut prover_state,
        global_statements_base,
        stacked_pcs_witness.inner_witness,
        &stacked_pcs_witness.global_polynomial.by_ref(),
    );

    WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()).prove2(
        &mut prover_state2,
        global_statements_base2,
        stacked_pcs_witness.inner_witness2,
        &stacked_pcs_witness.global_polynomial.by_ref(),
    );

    tracing::info!("total pow_grinding time: {} ms", pow_grinding_time().as_millis());
    reset_pow_grinding_time();

    Ok(ExecutionProof {
        proof: prover_state.into_proof(),
        proof2: prover_state2.into_proof(),
        metadata: Some(metadata),
    })
}
