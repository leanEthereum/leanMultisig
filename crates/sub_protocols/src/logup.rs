use crate::{ENDIANNESS_PIVOT_GKR, prove_gkr_quotient, verify_gkr_quotient};
use backend::*;
use lean_vm::*;
use std::borrow::Cow;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::ansi::Colorize;
use utils::*;

/// Materialize a `BusData` into a per-row column slice of length `n_rows`.
/// `Column` returns the underlying slice; the other variants allocate.
fn materialize_bus_data<'a>(data: &BusData, trace: &'a TableTrace, n_rows: usize) -> Cow<'a, [F]> {
    match data {
        BusData::Column(col) => Cow::Borrowed(&trace.columns[*col][..n_rows]),
        BusData::Constant(val) => Cow::Owned(vec![F::from_usize(*val); n_rows]),
        BusData::ColumnPlusOffset(col, off) => {
            let off_f = F::from_usize(*off);
            Cow::Owned(trace.columns[*col][..n_rows].iter().map(|v| *v + off_f).collect())
        }
        BusData::ImplicitIndex => Cow::Owned((0..n_rows).map(F::from_usize).collect()),
    }
}

/// Evaluate a `BusData` as a multilinear extension at `point`.
fn eval_bus_data_at_point(data: &BusData, trace: &TableTrace, point: &MultilinearPoint<EF>) -> EF {
    match data {
        BusData::Column(col) => trace.columns[*col].evaluate(point),
        BusData::Constant(val) => EF::from(F::from_usize(*val)),
        BusData::ColumnPlusOffset(col, off) => trace.columns[*col].evaluate(point) + EF::from(F::from_usize(*off)),
        BusData::ImplicitIndex => mle_of_01234567_etc(point),
    }
}

/// Iterate a bus's selector + data columns (deduplicated) and emit each MLE eval
/// at `point` to both `prover_state` (transcript) and `out` (for WHIR statements).
fn emit_bus_column_evals(
    bus: &Bus,
    trace: &TableTrace,
    point: &MultilinearPoint<EF>,
    out: &mut BTreeMap<ColIndex, EF>,
    prover_state: &mut impl FSProver<EF>,
) {
    for col in bus.referenced_columns() {
        if let std::collections::btree_map::Entry::Vacant(e) = out.entry(col) {
            let eval = trace.columns[col].evaluate(point);
            prover_state.add_extension_scalar(eval);
            e.insert(eval);
        }
    }
}

#[derive(Debug, PartialEq, Hash, Clone)]
pub struct GenericLogupStatements {
    pub bytecode_and_acc_point: MultilinearPoint<EF>,
    pub value_bytecode_acc: EF,
    pub bus_numerators_values: BTreeMap<Table, EF>,
    pub bus_denominators_values: BTreeMap<Table, EF>,
    pub gkr_point: Vec<EF>,
    pub columns_values: BTreeMap<Table, BTreeMap<ColIndex, EF>>,
    // Used in recursion
    pub total_gkr_n_vars: usize,
    pub bytecode_evaluation: Option<Evaluation<EF>>,
}

#[allow(clippy::too_many_arguments)]
#[instrument(skip_all)]
pub fn prove_generic_logup(
    prover_state: &mut impl FSProver<EF>,
    c: EF,
    alphas_eq_poly: &[EF],
    bytecode_multilinear: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> GenericLogupStatements {
    let memory_trace = &traces[&Table::memory()];
    let memory = &memory_trace.columns[MEMORY_COL_VALUE][..];
    let memory_acc = &memory_trace.columns[MEMORY_COL_ACC][..];
    assert!(memory.len().is_power_of_two());
    assert_eq!(memory.len(), memory_acc.len());
    assert!(memory.len() >= traces.values().map(|t| 1 << t.log_n_rows).max().unwrap());

    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let tables_log_heights: BTreeMap<Table, _> =
        traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_log_heights_sorted = sort_tables_by_height(&tables_log_heights);

    let total_active_len = compute_total_active_len(log_bytecode, &tables_log_heights_sorted);
    let total_gkr_n_vars = log2_ceil_usize(total_active_len);
    let mut numerators: Vec<F> = unsafe { uninitialized_vec(total_active_len) };
    let width = packing_width::<EF>();
    let mut denominators: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(total_active_len / width) };
    let c_packed = EFPacking::<EF>::from(c);
    let alphas_packed: Vec<EFPacking<EF>> = alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
    let alpha_last = *alphas_eq_poly.last().unwrap();
    let bytecode_contrib = EFPacking::<EF>::from(alpha_last * F::from_usize(LOGUP_BYTECODE_DOMAINSEP));
    // Per-bus fingerprint domain separator term.
    let dsep_contrib = |dsep: usize| EFPacking::<EF>::from(alpha_last * F::from_usize(dsep));

    let min_section_log = log_bytecode.min(tables_log_heights_sorted.last().unwrap().1);
    if min_section_log < ENDIANNESS_PIVOT_GKR {
        tracing::info!("TODO: suboptimal GKR pivot (could be improved).");
    }
    let pivot = ENDIANNESS_PIVOT_GKR.min(min_section_log);
    let chunk_size = 1usize << pivot;
    let chunk_shift = usize::BITS as usize - pivot;
    let chunk_mask = chunk_size - 1;
    let max_table_height = 1 << max_non_memory_log_height(&tables_log_heights_sorted);

    let src_idx = |p: usize, w: usize| -> usize {
        let x = p * width + w;
        (x & !chunk_mask) | ((x & chunk_mask).reverse_bits() >> chunk_shift)
    };

    let fill_num_from = |dst: &mut [F], src: &[F], neg: bool| {
        dst.par_chunks_exact_mut(chunk_size)
            .enumerate()
            .for_each(|(c, dst_chunk)| {
                let src_chunk = &src[c * chunk_size..][..chunk_size];
                for (i, slot) in dst_chunk.iter_mut().enumerate() {
                    let v = src_chunk[i.reverse_bits() >> chunk_shift];
                    *slot = if neg { -v } else { v };
                }
            });
    };

    let mut offset = 0;

    // Helper: emit one bus's GKR contribution at the current `offset`.
    let emit_bus_at = |numerators: &mut [F],
                       denominators: &mut [EFPacking<EF>],
                       offset: usize,
                       trace: &TableTrace,
                       bus: &Bus,
                       log_n_rows: usize| {
        let pull = matches!(bus.direction, BusDirection::Pull);
        // Fast path: a constant selector means every row contributes the same value,
        // so we can write directly without materializing a length-`1 << log_n_rows`
        // vector first (memory-access push buses use `Constant(1)`).
        if let BusData::Constant(val) = bus.selector {
            let mut v = F::from_usize(val);
            if pull {
                v = -v;
            }
            numerators[offset..][..1 << log_n_rows]
                .par_iter_mut()
                .for_each(|n| *n = v);
        } else {
            let selector_materialized = materialize_bus_data(&bus.selector, trace, 1 << log_n_rows);
            fill_num_from(
                &mut numerators[offset..][..1 << log_n_rows],
                &selector_materialized,
                pull,
            );
        }
        let bus_data_entries: &[BusData] = &bus.data;
        let contrib = dsep_contrib(bus.domain_sep);
        let denom_sub = bus.domain_sep == LOGUP_MEMORY_DOMAINSEP;
        fill_denoms(&mut denominators[offset / width..][..(1 << log_n_rows) / width], |p| {
            let mut bus_data = [PFPacking::<EF>::ZERO; MAX_PRECOMPILE_BUS_WIDTH];
            for (j, entry) in bus_data_entries.iter().enumerate() {
                bus_data[j] = match entry {
                    BusData::Column(col) => PFPacking::<EF>::from_fn(|w| trace.columns[*col][src_idx(p, w)]),
                    BusData::ColumnPlusOffset(col, off) => {
                        let off_f = F::from_usize(*off);
                        PFPacking::<EF>::from_fn(|w| trace.columns[*col][src_idx(p, w)] + off_f)
                    }
                    BusData::Constant(val) => PFPacking::<EF>::from(F::from_usize(*val)),
                    BusData::ImplicitIndex => PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w))),
                };
            }
            let fp = finger_print_packed::<EF>(contrib, &bus_data[..bus_data_entries.len()], &alphas_packed);
            if denom_sub { c_packed - fp } else { c_packed + fp }
        });
    };

    // The bytecode section is anchored right after Memory: Memory is the tallest table,
    // so placing the (padded) bytecode section after it keeps every subsequent
    // table offset divisible by its own `1 << log_n_rows` (required by `pref_at`).
    let bytecode_stride = N_INSTRUCTION_COLUMNS.next_power_of_two();
    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        if *table == Table::execution() {
            // Bytecode lookup (execution -> bytecode bus). Numerator = +1 per row.
            let pc_column = &trace.columns[COL_PC];
            let bytecode_columns = &trace.columns[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS];
            numerators[offset..][..1 << log_n_rows]
                .par_iter_mut()
                .for_each(|n| *n = F::ONE);
            fill_denoms(&mut denominators[offset / width..][..(1 << log_n_rows) / width], |p| {
                let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                for k in 0..N_INSTRUCTION_COLUMNS {
                    data[k] = PFPacking::<EF>::from_fn(|w| bytecode_columns[k][src_idx(p, w)]);
                }
                data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| pc_column[src_idx(p, w)]);
                c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed)
            });
            offset += 1 << log_n_rows;
        }

        for bus in table.buses() {
            emit_bus_at(&mut numerators, &mut denominators, offset, trace, &bus, log_n_rows);
            offset += 1 << log_n_rows;
        }

        if *table == Table::memory() {
            // Bytecode section (right after Memory). Numerator = -bytecode_acc per row.
            assert_eq!(1 << log_bytecode, bytecode_acc.len());
            fill_num_from(&mut numerators[offset..][..bytecode_acc.len()], bytecode_acc, true);
            fill_denoms(
                &mut denominators[offset / width..][..(1 << log_bytecode) / width],
                |p| {
                    let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                    for k in 0..N_INSTRUCTION_COLUMNS {
                        data[k] =
                            PFPacking::<EF>::from_fn(|w| bytecode_multilinear[src_idx(p, w) * bytecode_stride + k]);
                    }
                    data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w)));
                    c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed)
                },
            );
            if 1 << log_bytecode < max_table_height {
                numerators[offset + (1 << log_bytecode)..offset + max_table_height]
                    .par_iter_mut()
                    .for_each(|n| *n = F::ZERO);
                denominators[(offset + (1 << log_bytecode)) / width..(offset + max_table_height) / width]
                    .par_iter_mut()
                    .for_each(|d| *d = EFPacking::<EF>::ONE);
            }
            offset += max_table_height.max(1 << log_bytecode);
        }
    }

    assert_eq!(offset, total_active_len);
    tracing::info!(
        "{}",
        format!(
            "Logup data: {} = 2^{} * (1 + {:.2})",
            offset,
            total_gkr_n_vars - 1,
            (offset as f64) / (1 << (total_gkr_n_vars - 1)) as f64 - 1.0
        )
        .blue()
    );

    let (sum, claim_point_gkr) = prove_gkr_quotient::<EF>(
        prover_state,
        PFPacking::<EF>::pack_slice(&numerators),
        &denominators,
        pivot,
    );

    // sanity check
    assert_eq!(sum, EF::ZERO);

    let bytecode_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log_bytecode).to_vec());
    let value_bytecode_acc = bytecode_acc.evaluate(&bytecode_and_acc_point);

    // evaluation on bytecode itself can be done directly by the verifier

    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();

    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;
        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if *table == Table::execution() {
            let pc_column = &trace.columns[COL_PC];
            let bytecode_columns = trace.columns[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS]
                .iter()
                .collect::<Vec<_>>();

            let eval_on_pc = pc_column.evaluate(&inner_point);
            prover_state.add_extension_scalar(eval_on_pc);
            table_values.insert(COL_PC, eval_on_pc);

            let instr_evals = bytecode_columns
                .iter()
                .map(|col| col.evaluate(&inner_point))
                .collect::<Vec<_>>();
            prover_state.add_extension_scalars(&instr_evals);
            for (i, eval_on_instr_col) in instr_evals.iter().enumerate() {
                table_values.insert(N_RUNTIME_COLUMNS + i, *eval_on_instr_col);
            }
        }

        for bus in table.buses() {
            let is_precompile_bus = bus.domain_sep == LOGUP_PRECOMPILE_DOMAINSEP;
            if is_precompile_bus {
                let eval_on_selector =
                    eval_bus_data_at_point(&bus.selector, trace, &inner_point) * bus.direction.to_field_flag();
                prover_state.add_extension_scalar(eval_on_selector);

                let bus_data_evals: Vec<EF> = bus
                    .data
                    .iter()
                    .map(|entry| eval_bus_data_at_point(entry, trace, &inner_point))
                    .collect();
                let eval_on_data =
                    c + finger_print::<F, EF, EF>(F::from_usize(bus.domain_sep), &bus_data_evals, alphas_eq_poly);
                prover_state.add_extension_scalar(eval_on_data);

                bus_numerators_values.insert(*table, eval_on_selector);
                bus_denominators_values.insert(*table, eval_on_data);
            } else {
                emit_bus_column_evals(&bus, trace, &inner_point, &mut table_values, prover_state);
            }
        }

        columns_values.insert(*table, table_values);

        if *table == Table::memory() {
            // Bytecode_acc scalar emitted right after Memory (mirrors GKR-fill anchor).
            prover_state.add_extension_scalar(value_bytecode_acc);
        }
    }

    GenericLogupStatements {
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        gkr_point: claim_point_gkr.0,
        columns_values,
        total_gkr_n_vars,
        bytecode_evaluation: None,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn verify_generic_logup(
    verifier_state: &mut impl FSVerifier<EF>,
    c: EF,
    alphas: &[EF],
    alphas_eq_poly: &[EF],
    bytecode_multilinear: &[F],
    table_log_n_rows: &BTreeMap<Table, VarCount>,
) -> ProofResult<GenericLogupStatements> {
    let tables_heights_sorted = sort_tables_by_height(table_log_n_rows);
    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let total_gkr_n_vars = log2_ceil_usize(compute_total_active_len(log_bytecode, &tables_heights_sorted));

    let (sum, point_gkr, numerators_value, denominators_value) = verify_gkr_quotient(verifier_state, total_gkr_n_vars)?;

    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;

    let pref_at = |offset: usize, log_height: usize| {
        let n_missing = total_gkr_n_vars - log_height;
        let bits = to_big_endian_in_field::<EF>(offset >> log_height, n_missing);
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(point_gkr[..n_missing].to_vec()))
    };

    let mut offset = 0;
    let log_bytecode_padded = log_bytecode.max(max_non_memory_log_height(&tables_heights_sorted));
    let bytecode_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_bytecode).to_vec());

    let mut bytecode_point = bytecode_and_acc_point.0.clone();
    bytecode_point.extend(from_end(alphas, log2_ceil_usize(N_INSTRUCTION_COLUMNS)));
    let bytecode_point = MultilinearPoint(bytecode_point);
    let bytecode_value = bytecode_multilinear.evaluate(&bytecode_point);
    let bytecode_value_corrected = bytecode_value
        * alphas[..alphas.len() - log2_ceil_usize(N_INSTRUCTION_COLUMNS)]
            .iter()
            .map(|x| EF::ONE - *x)
            .product::<EF>();

    let mut bus_numerators_values: BTreeMap<Table, EF> = BTreeMap::new();
    let mut bus_denominators_values: BTreeMap<Table, EF> = BTreeMap::new();
    let mut columns_values: BTreeMap<Table, BTreeMap<ColIndex, EF>> = BTreeMap::new();
    // Memory is in `tables_heights_sorted`, so the bytecode-section block below runs exactly once.
    let mut value_bytecode_acc = EF::ZERO;

    for &(table, log_n_rows) in &tables_heights_sorted {
        let mut table_values = BTreeMap::<ColIndex, EF>::new();
        let inner_point = MultilinearPoint(from_end(&point_gkr, log_n_rows).to_vec());
        // Cached evaluation of the (0, 1, 2, …) MLE at this table's inner point —
        // referenced by every `BusData::ImplicitIndex` in this table's buses.
        let implicit_index_eval = std::cell::OnceCell::<EF>::new();

        if table == Table::execution() {
            // Bytecode lookup (special-cased, not a bus).
            let eval_on_pc = verifier_state.next_extension_scalar()?;
            table_values.insert(COL_PC, eval_on_pc);

            let instr_evals = verifier_state.next_extension_scalars_vec(N_INSTRUCTION_COLUMNS)?;
            for (i, eval_on_instr_col) in instr_evals.iter().enumerate() {
                table_values.insert(N_RUNTIME_COLUMNS + i, *eval_on_instr_col);
            }

            let pref = pref_at(offset, log_n_rows);
            retrieved_numerators_value += pref; // numerator is 1
            retrieved_denominators_value += pref
                * (c - finger_print(
                    F::from_usize(LOGUP_BYTECODE_DOMAINSEP),
                    &[instr_evals, vec![eval_on_pc]].concat(),
                    alphas_eq_poly,
                ));

            offset += 1 << log_n_rows;
        }

        for bus in table.buses() {
            let pref = pref_at(offset, log_n_rows);
            let is_precompile_bus = bus.domain_sep == LOGUP_PRECOMPILE_DOMAINSEP;
            if is_precompile_bus {
                // Read aggregated bus scalars (used by AIR sumcheck).
                let eval_on_selector = verifier_state.next_extension_scalar()?;
                retrieved_numerators_value += pref * eval_on_selector;

                let eval_on_data = verifier_state.next_extension_scalar()?;
                retrieved_denominators_value += pref * eval_on_data;

                bus_numerators_values.insert(table, eval_on_selector);
                bus_denominators_values.insert(table, eval_on_data);
            } else {
                for col in bus.referenced_columns() {
                    if let std::collections::btree_map::Entry::Vacant(e) = table_values.entry(col) {
                        let eval = verifier_state.next_extension_scalar()?;
                        e.insert(eval);
                    }
                }
                let bus_data_eval = |bd: &BusData| -> EF {
                    match bd {
                        BusData::Column(c) => table_values[c],
                        BusData::ColumnPlusOffset(c, off) => table_values[c] + EF::from(F::from_usize(*off)),
                        BusData::Constant(val) => EF::from(F::from_usize(*val)),
                        BusData::ImplicitIndex => {
                            *implicit_index_eval.get_or_init(|| mle_of_01234567_etc(&inner_point))
                        }
                    }
                };
                let selector_eval = bus_data_eval(&bus.selector) * bus.direction.to_field_flag();
                retrieved_numerators_value += pref * selector_eval;

                let data_evals: Vec<EF> = bus.data.iter().map(bus_data_eval).collect();
                let fp = finger_print(F::from_usize(bus.domain_sep), &data_evals, alphas_eq_poly);
                retrieved_denominators_value += pref * (c - fp);
            }
            offset += 1 << log_n_rows;
        }

        columns_values.insert(table, table_values);

        if table == Table::memory() {
            // Bytecode section (anchored right after Memory).
            let pref = pref_at(offset, log_bytecode);
            let pref_padded = pref_at(offset, log_bytecode_padded);

            value_bytecode_acc = verifier_state.next_extension_scalar()?;
            retrieved_numerators_value -= pref * value_bytecode_acc;

            let bytecode_index_value = mle_of_01234567_etc(&bytecode_and_acc_point);
            retrieved_denominators_value += pref
                * (c - (bytecode_value_corrected
                    + bytecode_index_value * alphas_eq_poly[N_INSTRUCTION_COLUMNS]
                    + *alphas_eq_poly.last().unwrap() * F::from_usize(LOGUP_BYTECODE_DOMAINSEP)));
            // Padding for bytecode.
            retrieved_denominators_value +=
                pref_padded * mle_of_zeros_then_ones(1 << log_bytecode, from_end(&point_gkr, log_bytecode_padded));

            offset += 1 << log_bytecode_padded;
        }
    }

    // Compensates for the final padding `xxx..xxx111...1`
    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &point_gkr);
    if retrieved_numerators_value != numerators_value {
        return Err(ProofError::InvalidProof);
    }
    if retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }

    Ok(GenericLogupStatements {
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        gkr_point: point_gkr.0,
        columns_values,
        total_gkr_n_vars,
        bytecode_evaluation: Some(Evaluation::new(bytecode_point, bytecode_value)),
    })
}

fn offset_for_table(table: &Table, log_n_rows: usize) -> usize {
    table.buses().len() << log_n_rows
}

pub fn max_non_memory_log_height(tables_heights_sorted: &[(Table, VarCount)]) -> VarCount {
    tables_heights_sorted
        .iter()
        .filter(|(t, _)| *t != Table::memory())
        .map(|(_, h)| *h)
        .max()
        .unwrap()
}

fn compute_total_active_len(log_bytecode: usize, tables_heights_sorted: &[(Table, VarCount)]) -> usize {
    let max_table_height = 1 << max_non_memory_log_height(tables_heights_sorted);
    let log_n_cycles = tables_heights_sorted
        .iter()
        .find(|(table, _)| *table == Table::execution())
        .unwrap()
        .1;
    (1 << log_bytecode).max(max_table_height) // bytecode section
        + (1 << log_n_cycles) // bytecode lookup (from exec table)
        + tables_heights_sorted
            .iter()
            .map(|(table, log_n_rows)| offset_for_table(table, *log_n_rows))
            .sum::<usize>()
}

#[inline]
fn fill_denoms<Build>(dst: &mut [EFPacking<EF>], build: Build)
where
    Build: Fn(usize) -> EFPacking<EF> + Sync,
{
    dst.par_iter_mut().enumerate().for_each(|(p, slot)| *slot = build(p));
}
