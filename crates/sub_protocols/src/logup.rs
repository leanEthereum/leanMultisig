use crate::{ENDIANNESS_PIVOT, prove_gkr_quotient, prove_gkr_quotient_from_packed_br_base, verify_gkr_quotient};
use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use tracing::{info_span, instrument};
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
    let _span = info_span!("Logup: Building initial numerators and denominators").entered();
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

    // `prove_gkr_quotient`'s SIMD phase-1 wants its inputs chunk-bit-reversed at
    // `chunk_log = min(ENDIANNESS_PIVOT, total_gkr_n_vars)`. We can avoid an
    // explicit ~17 ms bit-reverse pass over the filled buffers by writing each
    // section directly in bit-reversed layout — but only when the section
    // offsets *and* lengths are multiples of the chunk size.
    let log_memory = log2_strict_usize(memory.len());
    let pivot = ENDIANNESS_PIVOT.min(total_gkr_n_vars);
    let w_log = packing_log_width::<EF>();
    let chunk_size = 1usize << pivot;
    let packed_per_chunk = chunk_size / width;
    let chunk_shift = usize::BITS as usize - pivot;
    let use_bitrev = pivot > w_log
        && total_gkr_n_vars > w_log
        && log_memory >= pivot
        && log_bytecode >= pivot
        && tables_log_heights_sorted
            .iter()
            .all(|(_, log_n_rows)| *log_n_rows >= pivot);
    let max_table_height = 1 << tables_log_heights_sorted[0].1;

    let mut offset = 0;

    if use_bitrev {
        // ---- BIT-REVERSED FILLS ----
        // Each packed word at section-packed-index `p` has lane `w` reading
        // natural source offset `((p % packed_per_chunk) * width + w) bit-
        // reversed within the chunk`, plus `(p / packed_per_chunk) * chunk_size`.

        // Numerators: write scalar-by-scalar to scattered storage positions.
        // Denominators: write packed-word-by-packed-word, scatter-reading
        //               from natural sources via `storage_to_natural_bitrev`.

        // Memory section.
        numerators[offset..][..memory.len()]
            .par_chunks_exact_mut(chunk_size)
            .enumerate()
            .for_each(|(c, dst_chunk)| {
                let src_chunk = &memory_acc[c * chunk_size..][..chunk_size];
                for (s_within, slot) in dst_chunk.iter_mut().enumerate() {
                    *slot = -src_chunk[s_within.reverse_bits() >> chunk_shift];
                }
            });
        denominators_packed[offset / width..][..memory.len() / width]
            .par_iter_mut()
            .enumerate()
            .for_each(|(p, denom_packed)| {
                let p_chunk = p / packed_per_chunk;
                let p_within = p % packed_per_chunk;
                let chunk_base = p_chunk * chunk_size;
                *denom_packed = c_packed
                    - finger_print_packed::<EF>(
                        memory_contrib,
                        &[
                            PFPacking::<EF>::from_fn(|w| {
                                let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                memory[chunk_base + nat_off]
                            }),
                            PFPacking::<EF>::from_fn(|w| {
                                let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                F::from_usize(chunk_base + nat_off)
                            }),
                        ],
                        &alphas_packed,
                    );
            });
        offset += memory.len();

        // Bytecode section.
        numerators[offset..][..bytecode_acc.len()]
            .par_chunks_exact_mut(chunk_size)
            .enumerate()
            .for_each(|(c, dst_chunk)| {
                let src_chunk = &bytecode_acc[c * chunk_size..][..chunk_size];
                for (s_within, slot) in dst_chunk.iter_mut().enumerate() {
                    *slot = -src_chunk[s_within.reverse_bits() >> chunk_shift];
                }
            });
        {
            let bytecode_stride = N_INSTRUCTION_COLUMNS.next_power_of_two();
            denominators_packed[offset / width..][..(1 << log_bytecode) / width]
                .par_iter_mut()
                .enumerate()
                .for_each(|(p, denom_packed)| {
                    let p_chunk = p / packed_per_chunk;
                    let p_within = p % packed_per_chunk;
                    let chunk_base = p_chunk * chunk_size;
                    let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                    for k in 0..N_INSTRUCTION_COLUMNS {
                        data[k] = PFPacking::<EF>::from_fn(|w| {
                            let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                            bytecode_multilinear[(chunk_base + nat_off) * bytecode_stride + k]
                        });
                    }
                    data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| {
                        let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                        F::from_usize(chunk_base + nat_off)
                    });
                    *denom_packed = c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed);
                });
        }
        if 1 << log_bytecode < max_table_height {
            // Uniform padding — layout invariant.
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
                // Numerator = constant ONE — layout invariant.
                numerators[offset..][..1 << log_n_rows]
                    .par_iter_mut()
                    .for_each(|num| *num = F::ONE);
                denominators_packed[offset / width..][..(1 << log_n_rows) / width]
                    .par_iter_mut()
                    .enumerate()
                    .for_each(|(p, denom_packed)| {
                        let p_chunk = p / packed_per_chunk;
                        let p_within = p % packed_per_chunk;
                        let chunk_base = p_chunk * chunk_size;
                        let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                        for k in 0..N_INSTRUCTION_COLUMNS {
                            data[k] = PFPacking::<EF>::from_fn(|w| {
                                let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                bytecode_columns[k][chunk_base + nat_off]
                            });
                        }
                        data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| {
                            let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                            pc_column[chunk_base + nat_off]
                        });
                        *denom_packed = c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed);
                    });
                offset += 1 << log_n_rows;
            }

            // I] Bus
            let bus = table.bus();
            let selector = &trace.columns[bus.selector];
            let dir_sign = bus.direction;
            numerators[offset..][..1 << log_n_rows]
                .par_chunks_exact_mut(chunk_size)
                .enumerate()
                .for_each(|(c, dst_chunk)| {
                    let src_chunk = &selector[c * chunk_size..][..chunk_size];
                    for (s_within, slot) in dst_chunk.iter_mut().enumerate() {
                        let v = src_chunk[s_within.reverse_bits() >> chunk_shift];
                        *slot = F::from(match dir_sign {
                            BusDirection::Pull => -v,
                            BusDirection::Push => v,
                        });
                    }
                });
            {
                let bus_data_entries = &bus.data;
                denominators_packed[offset / width..][..(1 << log_n_rows) / width]
                    .par_iter_mut()
                    .enumerate()
                    .for_each(|(p, denom_packed)| {
                        let p_chunk = p / packed_per_chunk;
                        let p_within = p % packed_per_chunk;
                        let chunk_base = p_chunk * chunk_size;
                        let mut bus_data = [PFPacking::<EF>::ZERO; MAX_PRECOMPILE_BUS_WIDTH];
                        for (j, entry) in bus_data_entries.iter().enumerate() {
                            bus_data[j] = match entry {
                                BusData::Column(col) => PFPacking::<EF>::from_fn(|w| {
                                    let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                    trace.columns[*col][chunk_base + nat_off]
                                }),
                                BusData::Constant(val) => PFPacking::<EF>::from(F::from_usize(*val)),
                            };
                        }
                        *denom_packed = c_packed
                            + finger_print_packed::<EF>(
                                precompile_contrib,
                                &bus_data[..bus_data_entries.len()],
                                &alphas_packed,
                            );
                    });
            }
            offset += 1 << log_n_rows;

            // II] Lookup into memory
            let value_columns = table.lookup_value_columns(trace);
            let index_columns = table.lookup_index_columns(trace);
            for (col_index, col_values) in index_columns.iter().zip(&value_columns) {
                // Numerator = constant ONE — layout invariant.
                numerators[offset..][..col_values.len() << log_n_rows]
                    .par_iter_mut()
                    .for_each(|num| *num = F::ONE);
                {
                    let packed_chunk_size = (1 << log_n_rows) / width;
                    denominators_packed[offset / width..][..col_values.len() * packed_chunk_size]
                        .par_chunks_exact_mut(packed_chunk_size)
                        .enumerate()
                        .for_each(|(i, denom_chunk)| {
                            let i_field = F::from_usize(i);
                            denom_chunk.par_iter_mut().enumerate().for_each(|(p, denom_packed)| {
                                let p_chunk = p / packed_per_chunk;
                                let p_within = p % packed_per_chunk;
                                let chunk_base = p_chunk * chunk_size;
                                *denom_packed = c_packed
                                    - finger_print_packed::<EF>(
                                        memory_contrib,
                                        &[
                                            PFPacking::<EF>::from_fn(|w| {
                                                let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                                col_values[i][chunk_base + nat_off]
                                            }),
                                            PFPacking::<EF>::from_fn(|w| {
                                                let nat_off = (p_within * width + w).reverse_bits() >> chunk_shift;
                                                col_index[chunk_base + nat_off] + i_field
                                            }),
                                        ],
                                        &alphas_packed,
                                    );
                            });
                        });
                }
                offset += col_values.len() << log_n_rows;
            }
        }
    } else {
        // ---- NATURAL-ORDER FILLS (unchanged) ----
        // Memory: ...
        assert_eq!(memory.len(), memory_acc.len());
        numerators[offset..][..memory.len()]
            .par_iter_mut()
            .zip(memory_acc)
            .for_each(|(num, a)| *num = -*a); // Note the negative sign here
        denominators_packed[offset / width..][..memory.len() / width]
            .par_iter_mut()
            .enumerate()
            .for_each(|(chunk_idx, denom_packed)| {
                let base_i = chunk_idx * width;
                *denom_packed = c_packed
                    - finger_print_packed::<EF>(
                        memory_contrib,
                        &[
                            PFPacking::<EF>::from_fn(|w| memory[base_i + w]),
                            PFPacking::<EF>::from_fn(|w| F::from_usize(base_i + w)),
                        ],
                        &alphas_packed,
                    );
            });
        offset += memory.len();

        // Bytecode
        assert_eq!(1 << log_bytecode, bytecode_acc.len());
        numerators[offset..][..bytecode_acc.len()]
            .par_iter_mut()
            .zip(bytecode_acc)
            .for_each(|(num, a)| *num = -*a);
        {
            let bytecode_stride = N_INSTRUCTION_COLUMNS.next_power_of_two();
            denominators_packed[offset / width..][..(1 << log_bytecode) / width]
                .par_iter_mut()
                .enumerate()
                .for_each(|(chunk_idx, denom_packed)| {
                    let base_i = chunk_idx * width;
                    let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                    for k in 0..N_INSTRUCTION_COLUMNS {
                        data[k] =
                            PFPacking::<EF>::from_fn(|w| bytecode_multilinear[(base_i + w) * bytecode_stride + k]);
                    }
                    data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| F::from_usize(base_i + w));
                    *denom_packed = c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed);
                });
        }
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
                    .for_each(|num| *num = F::ONE);
                denominators_packed[offset / width..][..(1 << log_n_rows) / width]
                    .par_iter_mut()
                    .enumerate()
                    .for_each(|(chunk_idx, denom_packed)| {
                        let base_i = chunk_idx * width;
                        let mut data = [PFPacking::<EF>::ZERO; N_INSTRUCTION_COLUMNS + 1];
                        for k in 0..N_INSTRUCTION_COLUMNS {
                            data[k] = PFPacking::<EF>::from_fn(|w| bytecode_columns[k][base_i + w]);
                        }
                        data[N_INSTRUCTION_COLUMNS] = PFPacking::<EF>::from_fn(|w| pc_column[base_i + w]);
                        *denom_packed = c_packed - finger_print_packed::<EF>(bytecode_contrib, &data, &alphas_packed);
                    });
                offset += 1 << log_n_rows;
            }

            let bus = table.bus();
            numerators[offset..][..1 << log_n_rows]
                .par_iter_mut()
                .zip(&trace.columns[bus.selector])
                .for_each(|(num, selector)| {
                    *num = F::from(match bus.direction {
                        BusDirection::Pull => -*selector,
                        BusDirection::Push => *selector,
                    })
                });
            {
                let bus_data_entries = &bus.data;
                denominators_packed[offset / width..][..(1 << log_n_rows) / width]
                    .par_iter_mut()
                    .enumerate()
                    .for_each(|(chunk_idx, denom_packed)| {
                        let base_i = chunk_idx * width;
                        let mut bus_data = [PFPacking::<EF>::ZERO; MAX_PRECOMPILE_BUS_WIDTH];
                        for (j, entry) in bus_data_entries.iter().enumerate() {
                            bus_data[j] = match entry {
                                BusData::Column(col) => PFPacking::<EF>::from_fn(|w| trace.columns[*col][base_i + w]),
                                BusData::Constant(val) => PFPacking::<EF>::from(F::from_usize(*val)),
                            };
                        }
                        *denom_packed = c_packed
                            + finger_print_packed::<EF>(
                                precompile_contrib,
                                &bus_data[..bus_data_entries.len()],
                                &alphas_packed,
                            );
                    });
            }
            offset += 1 << log_n_rows;

            let value_columns = table.lookup_value_columns(trace);
            let index_columns = table.lookup_index_columns(trace);
            for (col_index, col_values) in index_columns.iter().zip(&value_columns) {
                numerators[offset..][..col_values.len() << log_n_rows]
                    .par_iter_mut()
                    .for_each(|num| *num = F::ONE);
                {
                    let packed_chunk_size = (1 << log_n_rows) / width;
                    denominators_packed[offset / width..][..col_values.len() * packed_chunk_size]
                        .par_chunks_exact_mut(packed_chunk_size)
                        .enumerate()
                        .for_each(|(i, denom_chunk)| {
                            let i_field = F::from_usize(i);
                            denom_chunk
                                .par_iter_mut()
                                .enumerate()
                                .for_each(|(chunk_idx, denom_packed)| {
                                    let base_j = chunk_idx * width;
                                    *denom_packed = c_packed
                                        - finger_print_packed::<EF>(
                                            memory_contrib,
                                            &[
                                                PFPacking::<EF>::from_fn(|w| col_values[i][base_j + w]),
                                                PFPacking::<EF>::from_fn(|w| col_index[base_j + w] + i_field),
                                            ],
                                            &alphas_packed,
                                        );
                                });
                        });
                }
                offset += col_values.len() << log_n_rows;
            }
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

    // Final padding: uniform EFPacking::ONE, same value at every storage slot,
    // so it's layout-invariant.
    denominators_packed[offset / width..]
        .par_iter_mut()
        .for_each(|d| *d = EFPacking::<EF>::ONE);

    std::mem::drop(_span);

    let (sum, claim_point_gkr, numerators_value, denominators_value) = if use_bitrev {
        // Data is already chunk-BR.  `numerators` (base field, F) is
        // scatter-filled in BR; we just pack it without reordering.
        let nums_br: Vec<PFPacking<EF>> = PFPacking::<EF>::pack_slice(&numerators).to_vec();
        prove_gkr_quotient_from_packed_br_base::<EF>(prover_state, nums_br, denominators_packed, total_gkr_n_vars)
    } else {
        let numerators_packed = MleRef::Base(&numerators).pack();
        let denom_ref = MleRef::<EF>::ExtensionPacked(&denominators_packed);
        prove_gkr_quotient(prover_state, &numerators_packed.by_ref(), &denom_ref)
    };

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

    // ... Rest of the tables:
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    for (table, _) in &tables_log_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if table == &Table::execution() {
            // 0] bytecode lookup
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

        // I] Bus (data flow between tables)
        let bus = table.bus();
        let eval_on_selector = trace.columns[bus.selector].evaluate(&inner_point) * bus.direction.to_field_flag();
        prover_state.add_extension_scalar(eval_on_selector);

        // `denominators_packed[...]` holds
        //   c + precompile_contrib + Σ alphas_eq_poly[i] * bus_data[i]
        // on this table's rows. MLE evaluation is affine in the stored
        // values, so we reconstruct the eval from the bus-data column evals
        // instead of reading `denominators_packed` (which won't stay in
        // natural order once we bit-reverse the fill below).
        let precompile_contrib_scalar = alpha_last * F::from_usize(LOGUP_PRECOMPILE_DOMAINSEP);
        let mut eval_on_data = c + precompile_contrib_scalar;
        for (i, entry) in bus.data.iter().enumerate() {
            let col_eval: EF = match entry {
                BusData::Column(col) => trace.columns[*col].evaluate(&inner_point),
                BusData::Constant(val) => EF::from(F::from_usize(*val)),
            };
            eval_on_data += alphas_eq_poly[i] * col_eval;
        }
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
