use std::collections::BTreeMap;

use crate::*;
use lean_vm::*;

use serde::{Deserialize, Serialize};
use sub_protocols::*;
use tracing::info_span;
use utils::ansi::Colorize;
use utils::{build_prover_state, from_end, padd_with_zero_to_next_power_of_two};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionProof {
    pub proof: Proof<F>,
    // benchmark / debug purpose
    #[serde(skip, default)]
    pub metadata: Option<ExecutionMetadata>,
}

/// Internal error: result of one attempt at `prove_with_known_hints`. Either succeeded, failed
/// for a normal reason, or the hints we used were too large — in which case the tight hints we
/// derived from the trial execution are passed back so the caller can retry.
enum AttemptOutcome {
    /// Carries `(proof, tight_hints)`: `tight_hints` is the normalized hint set that exactly
    /// matched the workload, suitable for caching so the next run skips both the heuristic and
    /// any retry.
    Ok(ExecutionProof, ExecutionHints),
    Err(ProverError),
    Overestimate(ExecutionHints),
}

/// Prove execution. Dry-runs once to discover trace / memory sizes, then proves with the
/// direct-write path. Existing callers don't need to change.
pub fn prove_execution(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
) -> Result<ExecutionProof, ProverError> {
    let hints = compute_hints_via_dry_run(bytecode, public_input, witness)?;
    // Dry-run hints exactly match the workload, so the strict path can't over-estimate.
    match prove_with_known_hints(bytecode, public_input, witness, whir_config, vm_profiler, hints, true) {
        AttemptOutcome::Ok(p, _) => Ok(p),
        AttemptOutcome::Err(e) => Err(e),
        AttemptOutcome::Overestimate(_) => unreachable!("dry-run-derived hints cannot over-estimate"),
    }
}

/// Prove execution with a caller-supplied size hint. If the hint turns out too small (any
/// `SlotColumn` overflows during execution), the prover catches the panic and transparently
/// falls back to the dry-run path. Hints that over-estimate are always safe.
pub fn prove_execution_hinted(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    hints: ExecutionHints,
) -> Result<(ExecutionProof, ExecutionHints), ProverError> {
    use std::panic::AssertUnwindSafe;

    install_slot_overflow_panic_filter();

    // Attempt 1: caller-provided hints, strict mode (abort early on over-estimate).
    let hints_attempt1 = hints.clone();
    let attempt = std::panic::catch_unwind(AssertUnwindSafe(|| {
        prove_with_known_hints(
            bytecode,
            public_input,
            witness,
            whir_config,
            vm_profiler,
            hints_attempt1,
            true,
        )
    }));
    let retry_hints: ExecutionHints = match attempt {
        Ok(AttemptOutcome::Ok(p, used)) => return Ok((p, used)),
        Ok(AttemptOutcome::Err(e)) => return Err(e),
        Ok(AttemptOutcome::Overestimate(tight)) => {
            let fmt_hints = |h: &ExecutionHints| {
                format!(
                    "memory 2^{}, exec 2^{}, ext_op 2^{}, poseidon 2^{}",
                    h.log_memory_size,
                    h.tables_log_n_rows[&Table::execution()],
                    h.tables_log_n_rows[&Table::extension_op()],
                    h.tables_log_n_rows[&Table::poseidon16()],
                )
            };
            let msg = format!(
                "ExecutionHints over-estimated (hint: {}; actual: {}); re-executing with tight hints. Tune `aggregation_hints` constants downward to avoid the retry.",
                fmt_hints(&hints),
                fmt_hints(&tight),
            );
            eprintln!("[lean_prover] {msg}");
            tracing::warn!("{msg}");
            tight
        }
        Err(payload) => {
            if let Some(detail) = slot_overflow_panic_detail(&payload) {
                let msg =
                    format!("ExecutionHints under-estimated a table/memory size ({detail}); falling back to dry-run.");
                eprintln!("[lean_prover] {msg}");
                tracing::warn!("{msg}");
                compute_hints_via_dry_run(bytecode, public_input, witness)?
            } else {
                std::panic::resume_unwind(payload);
            }
        }
    };

    // Attempt 2: tight hints (either from dry-run or from the over-estimate detection). Run in
    // non-strict mode — the retry hints exactly match the workload.
    match prove_with_known_hints(
        bytecode,
        public_input,
        witness,
        whir_config,
        vm_profiler,
        retry_hints,
        false,
    ) {
        AttemptOutcome::Ok(p, used) => Ok((p, used)),
        AttemptOutcome::Err(e) => Err(e),
        AttemptOutcome::Overestimate(_) => unreachable!("retry hints come from a trial execution; can't over-estimate"),
    }
}

/// If `payload` is a slot-overflow panic, return the panic message (for logging context);
/// otherwise `None` and the caller should re-raise.
fn slot_overflow_panic_detail(payload: &Box<dyn std::any::Any + Send>) -> Option<String> {
    if let Some(s) = payload.downcast_ref::<String>()
        && s.contains(SLOT_OVERFLOW_PANIC_MARKER)
    {
        return Some(s.clone());
    }
    if let Some(s) = payload.downcast_ref::<&'static str>()
        && s.contains(SLOT_OVERFLOW_PANIC_MARKER)
    {
        return Some((*s).to_string());
    }
    None
}

/// Install (once, process-wide) a panic hook that swallows the stderr printout for slot-overflow
/// panics so the hinted prover's fallback path stays quiet. Other panics fall through to the
/// previously-installed hook unchanged.
fn install_slot_overflow_panic_filter() {
    static ONCE: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    ONCE.get_or_init(|| {
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            let payload = info.payload();
            let is_slot_overflow = payload
                .downcast_ref::<String>()
                .map(|s| s.contains(SLOT_OVERFLOW_PANIC_MARKER))
                .unwrap_or(false)
                || payload
                    .downcast_ref::<&'static str>()
                    .map(|s| s.contains(SLOT_OVERFLOW_PANIC_MARKER))
                    .unwrap_or(false);
            if !is_slot_overflow {
                prev(info);
            }
        }));
    });
}

#[tracing::instrument(skip_all, name = "Dry-run for direct-write sizing")]
fn compute_hints_via_dry_run(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
) -> Result<ExecutionHints, ProverError> {
    let execution_result = try_execute_bytecode(bytecode, public_input, witness, false)?;
    let dry = get_execution_trace(bytecode, execution_result);
    let dry_memory_log = log2_strict_usize(dry.memory.len());
    let log_memory_size = dry_memory_log.max(MIN_LOG_MEMORY_SIZE).max(bytecode.log_size());
    let tables_log_n_rows: BTreeMap<Table, VarCount> = dry.traces.iter().map(|(t, tr)| (*t, tr.log_n_rows)).collect();
    drop(dry);
    Ok(ExecutionHints {
        log_memory_size,
        tables_log_n_rows,
    })
}

/// One attempt at proving with caller-supplied hints. When `strict` is true and the hints over-
/// estimate the workload, returns `AttemptOutcome::Overestimate(tight)` immediately after the
/// trial execution — *before* the expensive commit / sumcheck / WHIR phases — so the caller can
/// retry with the smaller (correct) layout.
fn prove_with_known_hints(
    bytecode: &Bytecode,
    public_input: &[F],
    witness: &ExecutionWitness,
    whir_config: &WhirConfigBuilder,
    vm_profiler: bool,
    hints: ExecutionHints,
    strict: bool,
) -> AttemptOutcome {
    macro_rules! r#try_ {
        ($e:expr) => {
            match $e {
                Ok(v) => v,
                Err(e) => return AttemptOutcome::Err(e.into()),
            }
        };
    }
    check_rate(whir_config.starting_log_inv_rate)
        .map_err(|err| panic!("{err}"))
        .unwrap();

    let log_memory_size = hints.log_memory_size.max(MIN_LOG_MEMORY_SIZE).max(bytecode.log_size());
    let mut tables_log_n_rows = hints.tables_log_n_rows;
    for table in ALL_TABLES {
        let entry = tables_log_n_rows.entry(table).or_insert(MIN_LOG_N_ROWS_PER_TABLE);
        *entry = (*entry).max(MIN_LOG_N_ROWS_PER_TABLE);
    }
    let exec_log = tables_log_n_rows[&Table::execution()];
    assert!(
        log_memory_size >= exec_log,
        "ExecutionHints: memory ({log_memory_size}) must be >= execution table ({exec_log})"
    );
    let max_table_log = tables_log_n_rows.values().copied().max().unwrap();
    assert!(
        exec_log >= max_table_log,
        "ExecutionHints: execution ({exec_log}) must be the largest table (got {max_table_log})"
    );

    for (table, &log_n_rows) in &tables_log_n_rows {
        assert!(log_n_rows >= MIN_LOG_N_ROWS_PER_TABLE, "missing padding");
        let log_limit = max_log_n_rows_per_table(table);
        if log_n_rows > log_limit {
            return AttemptOutcome::Err(
                TooBigTableError {
                    table_name: table.name(),
                    log_n_rows,
                    log_limit,
                }
                .into(),
            );
        }
    }

    // ─── Phase 2: allocate global polynomial + carve slots ─────────────────────────────────────
    let layout = GlobalPolyLayout::compute(log_memory_size, bytecode.log_size(), &tables_log_n_rows);
    let mut global_polynomial = F::zero_vec(1usize << layout.stacked_n_vars);

    let public_memory = padd_with_zero_to_next_power_of_two(public_input);
    let public_memory_size = public_memory.len();

    // Build slot-backed Memory: `values` points into `global_polynomial[layout.memory.range]`.
    // SAFETY: the slot region is disjoint from every other slot we hand out below, and
    // `global_polynomial` outlives `memory` (it's dropped last via `stacked_pcs_witness`).
    let memory = {
        let mem_slot: &mut [F] = &mut global_polynomial[layout.memory.clone()];
        unsafe { Memory::new_in_slot(mem_slot, &public_memory) }
    };

    // Build slot-backed traces: committed columns of every table point into the corresponding
    // (table, col) ranges in `global_polynomial`. Virtual columns stay owned. The borrow of
    // `global_polynomial` ends here; `traces` then holds raw pointers into its allocation.
    let traces = unsafe { build_slot_backed_traces(&mut global_polynomial, &layout) };

    // Pre-compute raw-pointer-backed accumulator slices so they survive across the `commit_*`
    // call that consumes `global_polynomial`. SAFETY: the four regions
    // (memory / memory_acc / bytecode_acc / each (table, col) slot) are disjoint by construction
    // (see `GlobalPolyLayout`), and the heap allocation backing `global_polynomial` is not freed
    // until `stacked_pcs_witness` is dropped at function end — long after every consumer here has
    // run. Moving `global_polynomial: Vec<F>` into `MleOwned::Base` does not relocate its heap.
    let global_ptr: *mut F = global_polynomial.as_mut_ptr();
    let memory_acc_ref: &mut [F] = unsafe {
        std::slice::from_raw_parts_mut(
            global_ptr.add(layout.memory_acc.start),
            layout.memory_acc.end - layout.memory_acc.start,
        )
    };
    let bytecode_acc_ref: &mut [F] = unsafe {
        std::slice::from_raw_parts_mut(
            global_ptr.add(layout.bytecode_acc.start),
            layout.bytecode_acc.end - layout.bytecode_acc.start,
        )
    };

    // ─── Phase 3: real execute, writing directly into the slots ────────────────────────────────
    let exec_outcome = info_span!("Witness generation").in_scope(|| -> Result<ExecutionTrace, ProverError> {
        let execution_result = info_span!("Executing bytecode").in_scope(|| {
            try_execute_bytecode_into(
                bytecode,
                public_input,
                witness,
                Some(memory),
                Trace::with_tables(traces),
                vm_profiler,
            )
        })?;
        Ok(info_span!("Building execution trace")
            .in_scope(|| get_execution_trace_with_overrides(bytecode, execution_result, &tables_log_n_rows)))
    });
    let ExecutionTrace {
        traces,
        public_memory_size: rt_public_memory_size,
        memory, // slot-backed view kept alive: its raw ptr is referenced below as `&memory[..]`
        metadata,
    } = r#try_!(exec_outcome);
    debug_assert_eq!(public_memory_size, rt_public_memory_size);
    let memory_len = 1usize << log_memory_size;

    // Detect over-estimated hints. `memory.len()` here is the *natural* padded size produced by
    // `get_execution_trace` (next power of two of post-execution memory usage). Tables expose
    // their natural sizes via `non_padded_n_rows`.
    let natural_log_memory = log2_strict_usize(memory.len())
        .max(MIN_LOG_MEMORY_SIZE)
        .max(bytecode.log_size());
    let natural_tables_log_n_rows: BTreeMap<Table, VarCount> = traces
        .iter()
        .map(|(t, tr)| {
            let natural = log2_ceil_usize(tr.non_padded_n_rows + 1).max(MIN_LOG_N_ROWS_PER_TABLE);
            (*t, natural)
        })
        .collect();
    let hints_too_large = log_memory_size > natural_log_memory
        || tables_log_n_rows.iter().any(|(t, &h)| h > natural_tables_log_n_rows[t]);
    if strict && hints_too_large {
        // Discard everything we've built and bubble the tight hints back so the caller can retry
        // with the right layout. This costs us one wasted execution, but the resulting proof is
        // smaller / faster to verify than the over-padded one would have been.
        drop(memory);
        drop(traces);
        drop(global_polynomial);
        let tight_log_memory = natural_log_memory;
        let mut tight_tables = natural_tables_log_n_rows;
        // Re-enforce the prover-side invariant `memory >= exec_table >= max(other tables)`.
        let exec_natural = tight_tables[&Table::execution()];
        let max_other = tight_tables.values().copied().max().unwrap();
        let tight_exec = exec_natural.max(max_other);
        tight_tables.insert(Table::execution(), tight_exec);
        let tight_log_memory = tight_log_memory.max(tight_exec);
        return AttemptOutcome::Overestimate(ExecutionHints {
            log_memory_size: tight_log_memory,
            tables_log_n_rows: tight_tables,
        });
    }

    // `get_execution_trace` pads memory only to the smallest power of two that fits the actual
    // execution. The stacked-layout memory region is sized to `1 << log_memory_size` (which
    // additionally satisfies the `MIN_LOG_MEMORY_SIZE` / `bytecode.log_size()` constraints), so
    // we extend to the slot capacity here. The slot's tail bytes are already zero from the
    // initial `F::zero_vec` allocation.
    let mut memory = memory;
    if memory.len() < memory_len {
        memory.resize(memory_len, F::ZERO);
    }
    debug_assert_eq!(memory.len(), memory_len);

    let mut prover_state = build_prover_state();
    prover_state.observe_scalars(public_input);
    prover_state.observe_scalars(&poseidon16_compress_pair(&bytecode.hash, &SNARK_DOMAIN_SEP));
    prover_state.add_base_scalars(
        &[
            vec![whir_config.starting_log_inv_rate, log_memory_size, public_input.len()],
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

    // ─── Phase 4: build memory_acc + bytecode_acc directly into their slots ────────────────────
    info_span!("Building memory access count").in_scope(|| {
        for (table, trace) in &traces {
            for lookup in table.lookups() {
                for i in &trace.columns[lookup.index] {
                    for j in 0..lookup.values.len() {
                        memory_acc_ref[i.to_usize() + j] += F::ONE;
                    }
                }
            }
        }
    });

    info_span!("Building bytecode access count").in_scope(|| {
        for pc in traces[&Table::execution()].columns[COL_PC].iter() {
            bytecode_acc_ref[pc.to_usize()] += F::ONE;
        }
    });

    // ─── Phase 5: commit the (already-built) global polynomial ─────────────────────────────────
    let stacked_pcs_witness =
        commit_prebuilt_global_polynomial(&mut prover_state, whir_config, global_polynomial, &layout);

    // logup (GKR)
    let logup_c = prover_state.sample();
    let logup_alphas = prover_state.sample_vec(log2_ceil_usize(max_bus_width_including_domainsep()));
    let logup_alphas_eq_poly = eval_eq(&logup_alphas);

    // `bytecode_acc_ref` covers the bytecode_acc *padded* to max(bytecode size, largest table
    // height) — that's the stacked-layout slot size. Logup expects the unpadded length, so we
    // slice down to `bytecode.padded_size()` here (the post-padding zeros are already in place
    // for the stacked commit).
    let bytecode_acc_logup = &bytecode_acc_ref[..bytecode.padded_size()];
    let logup_statements = prove_generic_logup(
        &mut prover_state,
        logup_c,
        &logup_alphas_eq_poly,
        &memory,
        memory_acc_ref,
        &bytecode.instructions_multilinear,
        bytecode_acc_logup,
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
                .map(|c| c.as_slice())
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
    }

    let sumcheck_air_point = info_span!("batched AIR sumcheck")
        .in_scope(|| prove_batched_air_sumcheck(&mut prover_state, &mut sessions, air_eta));

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
                (2 * memory_len) >> bytecode.log_size(),
                logup_statements.value_bytecode_acc,
            )],
        ),
    ];

    let global_statements_base = stacked_pcs_global_statements(
        stacked_pcs_witness.stacked_n_vars,
        log_memory_size,
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

    tracing::info!("total pow_grinding time: {} ms", pow_grinding_time().as_millis());
    reset_pow_grinding_time();

    let used_hints = ExecutionHints {
        log_memory_size,
        tables_log_n_rows: tables_log_n_rows.clone(),
    };
    AttemptOutcome::Ok(
        ExecutionProof {
            proof: prover_state.into_proof(),
            metadata: Some(metadata),
        },
        used_hints,
    )
}
