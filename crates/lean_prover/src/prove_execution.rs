use std::collections::BTreeMap;

use crate::*;
use lean_vm::*;

use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, from_end};
#[derive(Debug)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    // benchmark / debug purpose
    pub metadata: ExecutionMetadata,
}

pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> ExecutionProof {
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();
    let ExecutionTrace {
        traces,
        public_memory_size,
        mut memory, // padded with zeros to next power of two
        metadata,
    } = info_span!("Witness generation").in_scope(|| {
        let execution_result = info_span!("Executing bytecode")
            .in_scope(|| execute_bytecode(bytecode, public_input, witness, vm_profiler));
        info_span!("Building execution trace").in_scope(|| get_execution_trace(bytecode, execution_result))
    });

    // Memory must be at least MIN_LOG_MEMORY_SIZE and at least bytecode size
    // (required by the stacked polynomial ordering)
    let min_memory_size = (1 << MIN_LOG_MEMORY_SIZE).max(1 << bytecode.log_size());
    if memory.len() < min_memory_size {
        memory.resize(min_memory_size, F::ZERO);
    }
    let mut prover_state = build_prover_state();
    prover_state.observe_scalars(public_input);
    prover_state.observe_scalars(&poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP));
    prover_state.add_base_scalars(
        &[
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
        .collect::<Vec<_>>(),
    );

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
    let logup_alphas_eq_poly_packed = logup_alphas_eq_poly
        .iter()
        .map(|a| EFPacking::<EF>::from(*a))
        .collect::<Vec<_>>();

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
    let gkr_point = &logup_statements.gkr_point;
    let mut committed_statements: CommittedStatements = Default::default();
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
    }

    let bus_beta = prover_state.sample();
    let air_alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = air_alpha.powers().collect_n(max_air_constraints() + 1);
    let air_eta: EF = prover_state.sample();

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
    let shifted_rows: Vec<Vec<Vec<F>>> = tables_sorted
        .iter()
        .zip(&column_refs)
        .map(|((table, _), cols)| compute_shifted_columns(&table.down_column_indexes(), cols))
        .collect();

    let mut entries = Vec::with_capacity(tables_sorted.len());
    let mut eta_power = EF::ONE;
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

        let extra_data = ExtraDataForBuses {
            logup_alphas_eq_poly: logup_alphas_eq_poly.clone(),
            logup_alphas_eq_poly_packed: logup_alphas_eq_poly_packed.clone(),
            bus_beta,
            bus_beta_packed: EFPacking::<EF>::from(bus_beta),
            alpha_powers: air_alpha_powers.clone(),
        };

        let mut up_down: Vec<&[PF<EF>]> = column_refs[idx].to_vec();
        up_down.extend(shifted_rows[idx].iter().map(Vec::as_slice));
        let packed = MleGroupRef::<EF>::Base(up_down).pack();

        macro_rules! make_session {
            ($t:expr) => {{
                let session = SumcheckSessionState::new(packed, Some(eq_suffix), bus_final_value, *$t, extra_data);
                Box::new(session) as Box<dyn OuterSumcheckSession<EF> + '_>
            }};
        }
        let session = delegate_to_inner!(table => make_session);

        entries.push(BatchedProverEntry {
            session,
            eta_power,
            table_n_vars: *log_n_rows,
        });

        eta_power *= air_eta;
    }

    let all_challenges =
        info_span!("batched AIR sumcheck").in_scope(|| prove_batched_outer_sumcheck(&mut prover_state, &mut entries));

    for (idx, (table, log_n_rows)) in tables_sorted.iter().enumerate() {
        let inner_sums = entries[idx].session.finalize_inner_sums();
        prover_state.add_extension_scalars(&inner_sums);

        macro_rules! split {
            ($t:expr) => {{ split_air_inner_evals($t, &inner_sums, &all_challenges.0, *log_n_rows) }};
        }
        let claim = delegate_to_inner!(table => split);

        committed_statements.get_mut(table).unwrap().push(claim);
    }

    let public_memory_random_point = MultilinearPoint(prover_state.sample_vec(log2_strict_usize(public_memory_size)));
    let public_memory_eval = (&memory[..public_memory_size]).evaluate(&public_memory_random_point);

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

    let global_statements_base = stacked_pcs_global_statements(
        stacked_pcs_witness.stacked_n_vars,
        log2_strict_usize(memory.len()),
        bytecode.log_size(),
        previous_statements,
        &tables_log_heights,
        &committed_statements,
    );

    WhirConfig::new(whir_config, stacked_pcs_witness.global_polynomial.by_ref().n_vars()).prove(
        &mut prover_state,
        global_statements_base,
        stacked_pcs_witness.inner_witness,
        &stacked_pcs_witness.global_polynomial.by_ref(),
    );

    ExecutionProof {
        proof: prover_state.into_proof(),
        metadata,
    }
}
