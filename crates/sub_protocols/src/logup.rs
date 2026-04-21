use crate::{
    ENDIANNESS_PIVOT_GKR, bit_reverse_chunks_and_pack_ext, bit_reverse_chunks_and_pack_base, prove_gkr_quotient_br,
    verify_gkr_quotient,
};
use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use tracing::instrument;
use utils::ansi::Colorize;
use utils::*;

#[derive(Debug, PartialEq, Hash, Clone)]
pub struct GenericLogupStatements {
    pub memory_and_acc_point: MultilinearPoint<EF>,
    pub value_memory: EF,
    pub value_memory_acc: EF,
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
    memory: &[F],
    memory_acc: &[F],
    bytecode_multilinear: &[F],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> GenericLogupStatements {
    assert!(memory.len().is_power_of_two());
    assert_eq!(memory.len(), memory_acc.len());
    assert!(memory.len() >= traces.values().map(|t| 1 << t.log_n_rows).max().unwrap());

    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let tables_log_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_log_heights_sorted = sort_tables_by_height(&tables_log_heights);

    let total_gkr_n_vars = compute_total_gkr_n_vars(
        log2_strict_usize(memory.len()),
        log_bytecode,
        &tables_log_heights_sorted.iter().cloned().collect(),
    );
    let mut numerators = F::zero_vec(1 << total_gkr_n_vars);
    let width = packing_width::<EF>();
    let mut denominators_packed = EFPacking::<EF>::zero_vec((1 << total_gkr_n_vars) / width);
    let c_packed = EFPacking::<EF>::from(c);
    let alphas_packed: Vec<EFPacking<EF>> = alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
    let alpha_last = *alphas_eq_poly.last().unwrap();
    let memory_contrib = EFPacking::<EF>::from(alpha_last * F::from_usize(LOGUP_MEMORY_DOMAINSEP));
    let bytecode_contrib = EFPacking::<EF>::from(alpha_last * F::from_usize(LOGUP_BYTECODE_DOMAINSEP));
    let precompile_contrib = EFPacking::<EF>::from(alpha_last * F::from_usize(LOGUP_PRECOMPILE_DOMAINSEP));

    // `prove_gkr_quotient_br` expects inputs chunk-bit-reversed at
    // `chunk_log = min(ENDIANNESS_PIVOT, total_gkr_n_vars)`. Whenever every
    // section spans a whole number of chunks we write in BR layout directly
    // (SIMD-packed fills using `src_idx` to gather lanes), saving an explicit
    // BR pass. Otherwise we fill naturally and BR+pack at the end.
    let pivot = ENDIANNESS_PIVOT_GKR.min(total_gkr_n_vars);
    let w_log = packing_log_width::<EF>();
    let chunk_size = 1usize << pivot;
    let packed_per_chunk = chunk_size / width;
    let chunk_shift = usize::BITS as usize - pivot;
    let use_bitrev = pivot > w_log && total_gkr_n_vars > w_log && tables_log_heights_sorted.last().unwrap().1 <= pivot;
    let max_table_height = 1 << tables_log_heights_sorted[0].1;

    // Source-index mapping: packed-index `p`, lane `w` → natural source offset.
    // In BR layout each chunk's within-chunk indices are reversed; in natural
    // layout it's just `p*width + w`.
    let src_idx = |p: usize, w: usize| -> usize {
        if use_bitrev {
            let p_chunk = p / packed_per_chunk;
            let p_within = p % packed_per_chunk;
            p_chunk * chunk_size + ((p_within * width + w).reverse_bits() >> chunk_shift)
        } else {
            p * width + w
        }
    };

    // Fill `dst` (scalar F, length `len`) from `src` with optional sign.
    let fill_num_from = |dst: &mut [F], src: &[F], neg: bool| {
        if use_bitrev {
            dst.par_chunks_exact_mut(chunk_size)
                .enumerate()
                .for_each(|(c, dst_chunk)| {
                    let src_chunk = &src[c * chunk_size..][..chunk_size];
                    for (i, slot) in dst_chunk.iter_mut().enumerate() {
                        let v = src_chunk[i.reverse_bits() >> chunk_shift];
                        *slot = if neg { -v } else { v };
                    }
                });
        } else {
            dst.par_iter_mut()
                .zip(src)
                .for_each(|(slot, &v)| *slot = if neg { -v } else { v });
        }
    };

    // `fill_denoms` is a free generic fn (below) so `build` monomorphizes and
    // inlines — a closure let-binding would erase it to `&dyn Fn` and cost an
    // indirect call per element on ≥2^25 tables.

    let mut offset = 0;

    // Memory section.
    assert_eq!(memory.len(), memory_acc.len());
    fill_num_from(&mut numerators[offset..][..memory.len()], memory_acc, true);
    fill_denoms(
        &mut denominators_packed[offset / width..][..memory.len() / width],
        |p| {
            c_packed
                - finger_print_packed::<EF>(
                    memory_contrib,
                    &[
                        PFPacking::<EF>::from_fn(|w| memory[src_idx(p, w)]),
                        PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w))),
                    ],
                    &alphas_packed,
                )
        },
    );
    offset += memory.len();

    // Bytecode section.
    assert_eq!(1 << log_bytecode, bytecode_acc.len());
    fill_num_from(&mut numerators[offset..][..bytecode_acc.len()], bytecode_acc, true);
    let bytecode_stride = N_INSTRUCTION_COLUMNS.next_power_of_two();
    fill_denoms(
        &mut denominators_packed[offset / width..][..(1 << log_bytecode) / width],
        |p| {
            let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
            for k in 0..N_INSTRUCTION_COLUMNS {
                data[k] = PFPacking::<EF>::from_fn(|w| bytecode_multilinear[src_idx(p, w) * bytecode_stride + k]);
            }
            data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| F::from_usize(src_idx(p, w)));
            c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed)
        },
    );
    if 1 << log_bytecode < max_table_height {
        denominators_packed[(offset + (1 << log_bytecode)) / width..(offset + max_table_height) / width]
            .par_iter_mut()
            .for_each(|d| *d = EFPacking::<EF>::ONE);
    }
    offset += max_table_height.max(1 << log_bytecode);

    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        if *table == Table::execution() {
            let pc_column = &trace.columns[COL_PC];
            let bytecode_columns = &trace.columns[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS];
            numerators[offset..][..1 << log_n_rows]
                .par_iter_mut()
                .for_each(|n| *n = F::ONE);
            fill_denoms(
                &mut denominators_packed[offset / width..][..(1 << log_n_rows) / width],
                |p| {
                    let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                    for k in 0..N_INSTRUCTION_COLUMNS {
                        data[k] = PFPacking::<EF>::from_fn(|w| bytecode_columns[k][src_idx(p, w)]);
                    }
                    data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| pc_column[src_idx(p, w)]);
                    c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed)
                },
            );
            offset += 1 << log_n_rows;
        }

        // I] Bus
        let bus = table.bus();
        let selector = &trace.columns[bus.selector];
        let pull = matches!(bus.direction, BusDirection::Pull);
        fill_num_from(&mut numerators[offset..][..1 << log_n_rows], selector, pull);
        let bus_data_entries = &bus.data;
        fill_denoms(
            &mut denominators_packed[offset / width..][..(1 << log_n_rows) / width],
            |p| {
                let mut bus_data = [PFPacking::<EF>::ZERO; MAX_PRECOMPILE_BUS_WIDTH];
                for (j, entry) in bus_data_entries.iter().enumerate() {
                    bus_data[j] = match entry {
                        BusData::Column(col) => PFPacking::<EF>::from_fn(|w| trace.columns[*col][src_idx(p, w)]),
                        BusData::Constant(val) => PFPacking::<EF>::from(F::from_usize(*val)),
                    };
                }
                c_packed
                    + finger_print_packed::<EF>(precompile_contrib, &bus_data[..bus_data_entries.len()], &alphas_packed)
            },
        );
        offset += 1 << log_n_rows;

        // II] Lookup into memory
        let value_columns = table.lookup_value_columns(trace);
        let index_columns = table.lookup_index_columns(trace);
        for (col_index, col_values) in index_columns.iter().zip(&value_columns) {
            numerators[offset..][..col_values.len() << log_n_rows]
                .par_iter_mut()
                .for_each(|n| *n = F::ONE);
            let packed_chunk_size = (1 << log_n_rows) / width;
            denominators_packed[offset / width..][..col_values.len() * packed_chunk_size]
                .par_chunks_exact_mut(packed_chunk_size)
                .enumerate()
                .for_each(|(i, denom_chunk)| {
                    let i_field = F::from_usize(i);
                    denom_chunk.par_iter_mut().enumerate().for_each(|(p, slot)| {
                        *slot = c_packed
                            - finger_print_packed::<EF>(
                                memory_contrib,
                                &[
                                    PFPacking::<EF>::from_fn(|w| col_values[i][src_idx(p, w)]),
                                    PFPacking::<EF>::from_fn(|w| col_index[src_idx(p, w)] + i_field),
                                ],
                                &alphas_packed,
                            );
                    });
                });
            offset += col_values.len() << log_n_rows;
        }
    }

    assert_eq!(log2_ceil_usize(offset), total_gkr_n_vars);
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

    // Final padding: EFPacking::ONE everywhere (layout-invariant).
    denominators_packed[offset / width..]
        .par_iter_mut()
        .for_each(|d| *d = EFPacking::<EF>::ONE);

    // In the fallback (non-aligned) path we filled naturally; convert to
    // chunk-BR-packed via unpack + BR + pack. Borrowed in the happy path.
    let (nums_br_slice, dens_br_owned);
    let nums_br_owned;
    let dens_br_slice: &[EFPacking<EF>] = if use_bitrev {
        nums_br_slice = PFPacking::<EF>::pack_slice(&numerators);
        &denominators_packed
    } else {
        nums_br_owned = bit_reverse_chunks_and_pack_base::<EF>(&numerators, pivot);
        let dens_nat = unpack_extension::<EF>(&denominators_packed);
        dens_br_owned = bit_reverse_chunks_and_pack_ext::<EF>(&dens_nat, pivot);
        nums_br_slice = &nums_br_owned;
        &dens_br_owned
    };

    let (sum, claim_point_gkr, numerators_value, denominators_value) =
        prove_gkr_quotient_br::<EF>(prover_state, nums_br_slice, dens_br_slice, total_gkr_n_vars);

    let _ = (numerators_value, denominators_value); // TODO use it to avoid some computation below

    // sanity check
    assert_eq!(sum, EF::ZERO);

    // Memory: ...
    let memory_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log2_strict_usize(memory.len())).to_vec());
    let value_memory_acc = memory_acc.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory_acc);

    let value_memory = memory.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory);

    let bytecode_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log_bytecode).to_vec());
    let value_bytecode_acc = bytecode_acc.evaluate(&bytecode_and_acc_point);
    prover_state.add_extension_scalar(value_bytecode_acc);

    // evaluation on bytecode itself can be done directly by the verifier

    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if table == &Table::execution() {
            let pc_column = &trace.columns[COL_PC];
            let bytecode_columns = trace.columns[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS]
                .iter()
                .collect::<Vec<_>>();

            let eval_on_pc = pc_column.evaluate(&inner_point);
            prover_state.add_extension_scalar(eval_on_pc);
            assert!(!table_values.contains_key(&COL_PC));
            table_values.insert(COL_PC, eval_on_pc);

            let instr_evals = bytecode_columns
                .iter()
                .map(|col| col.evaluate(&inner_point))
                .collect::<Vec<_>>();
            prover_state.add_extension_scalars(&instr_evals);
            for (i, eval_on_instr_col) in instr_evals.iter().enumerate() {
                let global_index = N_RUNTIME_COLUMNS + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, *eval_on_instr_col);
            }
        }

        let bus = table.bus();
        let eval_on_selector = trace.columns[bus.selector].evaluate(&inner_point) * bus.direction.to_field_flag();
        prover_state.add_extension_scalar(eval_on_selector);

        let bus_data_evals: Vec<EF> = bus
            .data
            .iter()
            .map(|entry| match entry {
                BusData::Column(col) => trace.columns[*col].evaluate(&inner_point),
                BusData::Constant(val) => EF::from(F::from_usize(*val)),
            })
            .collect();
        let eval_on_data = c + finger_print::<F, EF, EF>(
            F::from_usize(LOGUP_PRECOMPILE_DOMAINSEP),
            &bus_data_evals,
            alphas_eq_poly,
        );
        prover_state.add_extension_scalar(eval_on_data);

        bus_numerators_values.insert(*table, eval_on_selector);
        bus_denominators_values.insert(*table, eval_on_data);

        // II] Lookup into memory
        for lookup in table.lookups() {
            let index_eval = trace.columns[lookup.index].evaluate(&inner_point);
            prover_state.add_extension_scalar(index_eval);
            assert!(!table_values.contains_key(&lookup.index));
            table_values.insert(lookup.index, index_eval);

            for col_index in &lookup.values {
                let value_eval = trace.columns[*col_index].evaluate(&inner_point);
                prover_state.add_extension_scalar(value_eval);
                assert!(!table_values.contains_key(col_index));
                table_values.insert(*col_index, value_eval);
            }
        }

        columns_values.insert(*table, table_values);
    }

    GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
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
    log_memory: usize,
    bytecode_multilinear: &[F],
    table_log_n_rows: &BTreeMap<Table, VarCount>,
) -> ProofResult<GenericLogupStatements> {
    let tables_heights_sorted = sort_tables_by_height(table_log_n_rows);
    let log_bytecode = log2_strict_usize(bytecode_multilinear.len() / N_INSTRUCTION_COLUMNS.next_power_of_two());
    let total_gkr_n_vars = compute_total_gkr_n_vars(
        log_memory,
        log_bytecode,
        &tables_heights_sorted.iter().cloned().collect(),
    );

    let (sum, point_gkr, numerators_value, denominators_value) = verify_gkr_quotient(verifier_state, total_gkr_n_vars)?;

    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;

    // Memory ...
    let memory_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_memory).to_vec());
    let bits = to_big_endian_in_field::<EF>(0, total_gkr_n_vars - log_memory);
    let pref =
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(point_gkr[..total_gkr_n_vars - log_memory].to_vec()));

    let value_memory_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_memory_acc;

    let value_memory = verifier_state.next_extension_scalar()?;
    let value_index = mle_of_01234567_etc(&memory_and_acc_point);
    retrieved_denominators_value += pref
        * (c - finger_print(
            F::from_usize(LOGUP_MEMORY_DOMAINSEP),
            &[value_memory, value_index],
            alphas_eq_poly,
        ));
    let mut offset = 1 << log_memory;

    // Bytecode
    let log_bytecode_padded = log_bytecode.max(tables_heights_sorted[0].1);
    let bytecode_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_bytecode).to_vec());
    let bits = to_big_endian_in_field::<EF>(offset >> log_bytecode, total_gkr_n_vars - log_bytecode);
    let pref = MultilinearPoint(bits)
        .eq_poly_outside(&MultilinearPoint(point_gkr[..total_gkr_n_vars - log_bytecode].to_vec()));
    let bits_padded =
        to_big_endian_in_field::<EF>(offset >> log_bytecode_padded, total_gkr_n_vars - log_bytecode_padded);
    let pref_padded = MultilinearPoint(bits_padded).eq_poly_outside(&MultilinearPoint(
        point_gkr[..total_gkr_n_vars - log_bytecode_padded].to_vec(),
    ));

    let value_bytecode_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_bytecode_acc;

    // Bytecode denominator - computed directly by verifier
    let bytecode_index_value = mle_of_01234567_etc(&bytecode_and_acc_point);

    let mut bytecode_point = bytecode_and_acc_point.0.clone();
    bytecode_point.extend(from_end(alphas, log2_ceil_usize(N_INSTRUCTION_COLUMNS)));
    let bytecode_point = MultilinearPoint(bytecode_point);
    let bytecode_value = bytecode_multilinear.evaluate(&bytecode_point);
    let bytecode_value_corrected = bytecode_value
        * alphas[..alphas.len() - log2_ceil_usize(N_INSTRUCTION_COLUMNS)]
            .iter()
            .map(|x| EF::ONE - *x)
            .product::<EF>();
    retrieved_denominators_value += pref
        * (c - (bytecode_value_corrected
            + bytecode_index_value * alphas_eq_poly[N_INSTRUCTION_COLUMNS]
            + *alphas_eq_poly.last().unwrap() * F::from_usize(LOGUP_BYTECODE_DOMAINSEP)));
    // Padding for bytecode
    retrieved_denominators_value +=
        pref_padded * mle_of_zeros_then_ones(1 << log_bytecode, from_end(&point_gkr, log_bytecode_padded));
    offset += 1 << log_bytecode_padded;

    // ... Rest of the tables:
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    for &(table, log_n_rows) in &tables_heights_sorted {
        let n_missing_vars = total_gkr_n_vars - log_n_rows;
        let missing_point = MultilinearPoint(point_gkr[..n_missing_vars].to_vec());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if table == Table::execution() {
            // 0] bytecode lookup
            let eval_on_pc = verifier_state.next_extension_scalar()?;
            table_values.insert(COL_PC, eval_on_pc);

            let instr_evals = verifier_state.next_extension_scalars_vec(N_INSTRUCTION_COLUMNS)?;
            for (i, eval_on_instr_col) in instr_evals.iter().enumerate() {
                let global_index = N_RUNTIME_COLUMNS + i;
                table_values.insert(global_index, *eval_on_instr_col);
            }

            let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
            let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
            retrieved_numerators_value += pref; // numerator is 1
            retrieved_denominators_value += pref
                * (c - finger_print(
                    F::from_usize(LOGUP_BYTECODE_DOMAINSEP),
                    &[instr_evals, vec![eval_on_pc]].concat(),
                    alphas_eq_poly,
                ));

            offset += 1 << log_n_rows;
        }

        // I] Bus (data flow between tables)
        let eval_on_selector = verifier_state.next_extension_scalar()?;

        let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
        let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
        retrieved_numerators_value += pref * eval_on_selector;

        let eval_on_data = verifier_state.next_extension_scalar()?;
        retrieved_denominators_value += pref * eval_on_data;

        bus_numerators_values.insert(table, eval_on_selector);
        bus_denominators_values.insert(table, eval_on_data);

        offset += 1 << log_n_rows;

        // II] Lookup into memory
        for lookup in table.lookups() {
            let index_eval = verifier_state.next_extension_scalar()?;
            assert!(!table_values.contains_key(&lookup.index));
            table_values.insert(lookup.index, index_eval);

            for (i, col_index) in lookup.values.iter().enumerate() {
                let value_eval = verifier_state.next_extension_scalar()?;
                assert!(!table_values.contains_key(col_index));
                table_values.insert(*col_index, value_eval);

                let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
                let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                retrieved_numerators_value += pref; // numerator is 1
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        F::from_usize(LOGUP_MEMORY_DOMAINSEP),
                        &[value_eval, index_eval + F::from_usize(i)],
                        alphas_eq_poly,
                    ));
                offset += 1 << log_n_rows;
            }
        }

        columns_values.insert(table, table_values);
    }

    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &point_gkr); // to compensate for the final padding: XYZ111111...1
    if retrieved_numerators_value != numerators_value {
        return Err(ProofError::InvalidProof);
    }
    if retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }

    Ok(GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
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
    let num_cols = table.lookups().iter().map(|l| l.values.len()).sum::<usize>() + 1; // +1 for the bus
    num_cols << log_n_rows
}

fn compute_total_gkr_n_vars(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> usize {
    let max_table_height = 1 << tables_log_heights.values().copied().max().unwrap();
    let total_len = (1 << log_memory)
        + (1 << log_bytecode).max(max_table_height) + (1 << tables_log_heights[&Table::execution()]) // bytecode
        + tables_log_heights
            .iter()
            .map(|(table, log_n_rows)| offset_for_table(table, *log_n_rows))
            .sum::<usize>();
    log2_ceil_usize(total_len)
}

#[inline]
fn fill_denoms<Build>(dst: &mut [EFPacking<EF>], build: Build)
where
    Build: Fn(usize) -> EFPacking<EF> + Sync,
{
    dst.par_iter_mut().enumerate().for_each(|(p, slot)| *slot = build(p));
}
