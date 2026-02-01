use crate::{prove_gkr_quotient, verify_gkr_quotient};
use lean_vm::*;
use multilinear_toolkit::prelude::*;
use std::collections::BTreeMap;
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
    pub points: BTreeMap<Table, MultilinearPoint<EF>>,
    pub columns_values: BTreeMap<Table, BTreeMap<ColIndex, EF>>,
    // Used in recursion
    pub total_n_vars: usize,
}

#[allow(clippy::too_many_arguments)]
pub fn prove_generic_logup(
    prover_state: &mut impl FSProver<EF>,
    c: EF,
    alphas_eq_poly: &[EF],
    memory: &[F],
    memory_acc: &[F],
    bytecode: &[[F; N_INSTRUCTION_COLUMNS]],
    bytecode_acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
) -> GenericLogupStatements {
    assert!(memory[0].is_zero());
    assert!(memory.len().is_power_of_two());
    assert_eq!(memory.len(), memory_acc.len());
    assert!(memory.len() >= traces.values().map(|t| 1 << t.log_n_rows).max().unwrap());

    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);

    let total_n_vars = compute_total_n_vars(
        log2_strict_usize(memory.len()),
        log2_strict_usize(bytecode.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut numerators = EF::zero_vec(1 << total_n_vars);
    let mut denominators = EF::zero_vec(1 << total_n_vars);

    let mut offset = 0;

    // Memory: ...
    assert_eq!(memory.len(), memory_acc.len());
    numerators[offset..][..memory.len()]
        .par_iter_mut()
        .zip(memory_acc) // TODO embedding overhead
        .for_each(|(num, a)| *num = EF::from(-*a)); // Note the negative sign here 
    denominators[offset..][..memory.len()]
        .par_iter_mut()
        .zip(memory.par_iter().enumerate())
        .for_each(|(denom, (i, &mem_value))| {
            *denom = c - finger_print(
                F::from_usize(MEMORY_TABLE_INDEX),
                &[mem_value, F::from_usize(i)],
                alphas_eq_poly,
            )
        });
    offset += memory.len();

    // Bytecode
    assert_eq!(bytecode.len(), bytecode_acc.len());
    numerators[offset..][..bytecode_acc.len()]
        .par_iter_mut()
        .zip(bytecode_acc) // TODO embedding overhead
        .for_each(|(num, a)| *num = EF::from(-*a)); // Note the negative sign here
    denominators[offset..][..bytecode.len()]
        .par_iter_mut()
        .zip(bytecode.par_iter().enumerate())
        .for_each(|(denom, (i, &instr))| {
            *denom = c - finger_print(
                F::from_usize(BYTECODE_TABLE_INDEX),
                &[instr.to_vec(), vec![F::from_usize(i)]].concat(),
                alphas_eq_poly,
            )
        });
    let max_table_height = 1 << tables_heights_sorted[0].1;
    if bytecode.len() < max_table_height {
        // padding
        denominators[offset + bytecode.len()..offset + max_table_height]
            .par_iter_mut()
            .for_each(|d| *d = EF::ONE);
    }
    offset += max_table_height.max(bytecode.len());

    // ... Rest of the tables:
    for (table, _) in &tables_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        if *table == Table::execution() {
            // 0] bytecode lookup
            let pc_column = &trace.base[COL_PC];
            let bytecode_columns = trace.base[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS]
                .iter()
                .collect::<Vec<_>>();
            numerators[offset..][..1 << log_n_rows].par_iter_mut().for_each(|num| {
                *num = EF::ONE;
            }); // TODO embedding overhead
            denominators[offset..][..1 << log_n_rows]
                .par_iter_mut()
                .enumerate()
                .for_each(|(i, denom)| {
                    let mut data = vec![];
                    for col in &bytecode_columns {
                        data.push(col[i]);
                    }
                    data.push(pc_column[i]);
                    *denom = c - finger_print(F::from_usize(BYTECODE_TABLE_INDEX), &data, alphas_eq_poly)
                });
            offset += 1 << log_n_rows;
        }

        // I] Bus (data flow between tables)
        let bus = table.bus();
        numerators[offset..][..1 << log_n_rows]
            .par_iter_mut()
            .zip(&trace.base[bus.selector])
            .for_each(|(num, selector)| {
                *num = EF::from(match bus.direction {
                    BusDirection::Pull => -*selector,
                    BusDirection::Push => *selector,
                })
            }); // TODO embedding overhead
        denominators[offset..][..1 << log_n_rows]
            .par_iter_mut()
            .enumerate()
            .for_each(|(i, denom)| {
                *denom = {
                    c + finger_print(
                        match &bus.table {
                            BusTable::Constant(table) => table.embed(),
                            BusTable::Variable(col) => trace.base[*col][i],
                        },
                        bus.data
                            .iter()
                            .map(|col| trace.base[*col][i])
                            .collect::<Vec<_>>()
                            .as_slice(),
                        alphas_eq_poly,
                    )
                }
            });

        offset += 1 << log_n_rows;

        // II] Lookup into memory
        let mut value_columns_f = Vec::<Vec<_>>::new();
        for cols_f in table.lookup_f_value_columns(trace) {
            value_columns_f.push(cols_f.iter().map(|s| VecOrSlice::Slice(s)).collect());
        }
        let mut value_columns_ef = Vec::<Vec<_>>::new();
        for col_ef in table.lookup_ef_value_columns(trace) {
            value_columns_ef.push(
                transpose_slice_to_basis_coefficients::<PF<EF>, EF>(col_ef)
                    .into_iter()
                    .map(VecOrSlice::Vec)
                    .collect(),
            );
        }
        for (index_columns, value_columns) in [
            (table.lookup_index_columns_f(trace), &value_columns_f),
            (table.lookup_index_columns_ef(trace), &value_columns_ef),
        ] {
            for (col_index, col_values) in index_columns.iter().zip(value_columns) {
                numerators[offset..][..col_values.len() << log_n_rows]
                    .par_iter_mut()
                    .for_each(|num| {
                        *num = EF::ONE;
                    }); // TODO embedding overhead
                denominators[offset..][..col_values.len() << log_n_rows]
                    .par_chunks_exact_mut(1 << log_n_rows)
                    .enumerate()
                    .for_each(|(i, denom_chunk)| {
                        let i_field = F::from_usize(i);
                        denom_chunk.par_iter_mut().enumerate().for_each(|(j, denom)| {
                            let index = col_index[j] + i_field;
                            let mem_value = col_values[i].as_slice()[j];
                            *denom =
                                c - finger_print(F::from_usize(MEMORY_TABLE_INDEX), &[mem_value, index], alphas_eq_poly)
                        });
                    });
                offset += col_values.len() << log_n_rows;
            }
        }
    }

    assert_eq!(log2_ceil_usize(offset), total_n_vars);
    tracing::info!("Logup data: {} = 2^{:.2}", offset, (offset as f64).log2());

    denominators[offset..].par_iter_mut().for_each(|d| *d = EF::ONE); // padding

    // TODO pack directly
    let numerators_packed = MleRef::Extension(&numerators).pack();
    let denominators_packed = MleRef::Extension(&denominators).pack();

    let (sum, claim_point_gkr, numerators_value, denominators_value) =
        prove_gkr_quotient(prover_state, &numerators_packed.by_ref(), &denominators_packed.by_ref());

    let _ = (numerators_value, denominators_value); // TODO use it to avoid some computation below

    // sanity check
    assert_eq!(sum, EF::ZERO);

    // Memory: ...
    let memory_and_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log2_strict_usize(memory.len())).to_vec());
    let value_memory_acc = memory_acc.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory_acc);

    let value_memory = memory.evaluate(&memory_and_acc_point);
    prover_state.add_extension_scalar(value_memory);

    let bytecode_and_acc_point =
        MultilinearPoint(from_end(&claim_point_gkr, log2_strict_usize(bytecode.len())).to_vec());
    let value_bytecode_acc = bytecode_acc.evaluate(&bytecode_and_acc_point);
    prover_state.add_extension_scalar(value_bytecode_acc);

    // evaluation on bytecode itself can be done directly by the verifier

    // ... Rest of the tables:
    let mut points = BTreeMap::new();
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    let mut offset = memory.len() + max_table_height.max(bytecode.len());
    for (table, _) in &tables_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        points.insert(*table, inner_point.clone());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if table == &Table::execution() {
            // 0] bytecode lookup
            let pc_column = &trace.base[COL_PC];
            let bytecode_columns = trace.base[N_RUNTIME_COLUMNS..][..N_INSTRUCTION_COLUMNS]
                .iter()
                .collect::<Vec<_>>();

            let eval_on_pc = pc_column.evaluate(&inner_point);
            prover_state.add_extension_scalar(eval_on_pc);
            assert!(!table_values.contains_key(&COL_PC));
            table_values.insert(COL_PC, eval_on_pc);

            for (i, col) in bytecode_columns.iter().enumerate() {
                let eval_on_instr_col = col.evaluate(&inner_point);
                prover_state.add_extension_scalar(eval_on_instr_col);
                let global_index = N_RUNTIME_COLUMNS + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, eval_on_instr_col);
            }

            offset += 1 << log_n_rows;
        }

        // I] Bus (data flow between tables)
        let eval_on_selector =
            trace.base[table.bus().selector].evaluate(&inner_point) * table.bus().direction.to_field_flag();
        prover_state.add_extension_scalar(eval_on_selector);

        let eval_on_data = (&denominators[offset..][..1 << log_n_rows]).evaluate(&inner_point);
        prover_state.add_extension_scalar(eval_on_data);

        bus_numerators_values.insert(*table, eval_on_selector);
        bus_denominators_values.insert(*table, eval_on_data);

        // II] Lookup into memory
        for lookup_f in table.lookups_f() {
            let index_eval = trace.base[lookup_f.index].evaluate(&inner_point);
            prover_state.add_extension_scalar(index_eval);
            assert!(!table_values.contains_key(&lookup_f.index));
            table_values.insert(lookup_f.index, index_eval);

            for col_index in &lookup_f.values {
                let value_eval = trace.base[*col_index].evaluate(&inner_point);
                prover_state.add_extension_scalar(value_eval);
                assert!(!table_values.contains_key(col_index));
                table_values.insert(*col_index, value_eval);
            }
        }

        for lookup_ef in table.lookups_ef() {
            let index_eval = trace.base[lookup_ef.index].evaluate(&inner_point);
            prover_state.add_extension_scalar(index_eval);
            assert_eq!(table_values.get(&lookup_ef.index).unwrap_or(&index_eval), &index_eval);
            table_values.insert(lookup_ef.index, index_eval);

            let col_ef = &trace.ext[lookup_ef.values];

            for (i, col) in transpose_slice_to_basis_coefficients::<PF<EF>, EF>(col_ef)
                .iter()
                .enumerate()
            {
                let value_eval = col.evaluate(&inner_point);
                prover_state.add_extension_scalar(value_eval);
                let global_index = table.n_columns_f_air() + lookup_ef.values * DIMENSION + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, value_eval);
            }
        }
        points.insert(*table, inner_point);
        columns_values.insert(*table, table_values);

        offset += offset_for_table(table, log_n_rows);
    }

    GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        points,
        columns_values,
        total_n_vars,
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
    let total_n_vars = compute_total_n_vars(
        log_memory,
        log_bytecode,
        &tables_heights_sorted.iter().cloned().collect(),
    );

    let (sum, point_gkr, numerators_value, denominators_value) = verify_gkr_quotient(verifier_state, total_n_vars)?;

    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;

    // Memory ...
    let memory_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_memory).to_vec());
    let bits = to_big_endian_in_field::<EF>(0, total_n_vars - log_memory);
    let pref =
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(point_gkr[..total_n_vars - log_memory].to_vec()));

    let value_memory_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_memory_acc;

    let value_memory = verifier_state.next_extension_scalar()?;
    let value_index = mle_of_01234567_etc(&memory_and_acc_point);
    retrieved_denominators_value += pref
        * (c - finger_print(
            F::from_usize(MEMORY_TABLE_INDEX),
            &[value_memory, value_index],
            alphas_eq_poly,
        ));
    let mut offset = 1 << log_memory;

    // Bytecode
    let log_bytecode_padded = log_bytecode.max(tables_heights_sorted[0].1);
    let bytecode_and_acc_point = MultilinearPoint(from_end(&point_gkr, log_bytecode).to_vec());
    let bits = to_big_endian_in_field::<EF>(offset >> log_bytecode, total_n_vars - log_bytecode);
    let pref =
        MultilinearPoint(bits).eq_poly_outside(&MultilinearPoint(point_gkr[..total_n_vars - log_bytecode].to_vec()));
    let bits_padded = to_big_endian_in_field::<EF>(offset >> log_bytecode_padded, total_n_vars - log_bytecode_padded);
    let pref_padded = MultilinearPoint(bits_padded).eq_poly_outside(&MultilinearPoint(
        point_gkr[..total_n_vars - log_bytecode_padded].to_vec(),
    ));

    let value_bytecode_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_bytecode_acc;

    // Bytecode denominator - computed directly by verifier
    let bytecode_index_value = mle_of_01234567_etc(&bytecode_and_acc_point);

    let mut bytecode_evaluation_point = bytecode_and_acc_point.0.clone();
    bytecode_evaluation_point.extend(from_end(alphas, log2_ceil_usize(N_INSTRUCTION_COLUMNS)));
    let mut bytecode_value = bytecode_multilinear.evaluate(&MultilinearPoint(bytecode_evaluation_point));
    bytecode_value *= alphas[..alphas.len() - log2_ceil_usize(N_INSTRUCTION_COLUMNS)]
        .iter()
        .map(|x| EF::ONE - *x)
        .product::<EF>();
    retrieved_denominators_value += pref
        * (c - (bytecode_value
            + bytecode_index_value * alphas_eq_poly[N_INSTRUCTION_COLUMNS]
            + *alphas_eq_poly.last().unwrap() * F::from_usize(BYTECODE_TABLE_INDEX)));
    // Padding for bytecode
    retrieved_denominators_value +=
        pref_padded * mle_of_zeros_then_ones(1 << log_bytecode, &from_end(&point_gkr, log_bytecode_padded));
    offset += 1 << log_bytecode_padded;

    // ... Rest of the tables:
    let mut points = BTreeMap::new();
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_values = BTreeMap::new();

    for &(table, log_n_rows) in &tables_heights_sorted {
        let n_missing_vars = total_n_vars - log_n_rows;
        let inner_point = MultilinearPoint(from_end(&point_gkr, log_n_rows).to_vec());
        let missing_point = MultilinearPoint(point_gkr[..n_missing_vars].to_vec());

        points.insert(table, inner_point.clone());
        let mut table_values = BTreeMap::<ColIndex, EF>::new();

        if table == Table::execution() {
            // 0] bytecode lookup
            let eval_on_pc = verifier_state.next_extension_scalar()?;
            table_values.insert(COL_PC, eval_on_pc);

            let mut instr_evals = Vec::with_capacity(N_INSTRUCTION_COLUMNS);
            for i in 0..N_INSTRUCTION_COLUMNS {
                let eval_on_instr_col = verifier_state.next_extension_scalar()?;
                let global_index = N_RUNTIME_COLUMNS + i;
                table_values.insert(global_index, eval_on_instr_col);
                instr_evals.push(eval_on_instr_col);
            }

            let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
            let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
            retrieved_numerators_value += pref; // numerator is 1
            retrieved_denominators_value += pref
                * (c - finger_print(
                    F::from_usize(BYTECODE_TABLE_INDEX),
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
        for lookup_f in table.lookups_f() {
            let index_eval = verifier_state.next_extension_scalar()?;
            assert!(!table_values.contains_key(&lookup_f.index));
            table_values.insert(lookup_f.index, index_eval);

            for (i, col_index) in lookup_f.values.iter().enumerate() {
                let value_eval = verifier_state.next_extension_scalar()?;
                assert!(!table_values.contains_key(col_index));
                table_values.insert(*col_index, value_eval);

                let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
                let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                retrieved_numerators_value += pref; // numerator is 1
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        F::from_usize(MEMORY_TABLE_INDEX),
                        &[value_eval, index_eval + F::from_usize(i)],
                        alphas_eq_poly,
                    ));
                offset += 1 << log_n_rows;
            }
        }

        for lookup_ef in table.lookups_ef() {
            let index_eval = verifier_state.next_extension_scalar()?;
            assert_eq!(table_values.get(&lookup_ef.index).unwrap_or(&index_eval), &index_eval);
            table_values.insert(lookup_ef.index, index_eval);

            for i in 0..DIMENSION {
                let value_eval = verifier_state.next_extension_scalar()?;

                let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
                let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                retrieved_numerators_value += pref;
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        F::from_usize(MEMORY_TABLE_INDEX),
                        &[value_eval, index_eval + F::from_usize(i)],
                        alphas_eq_poly,
                    ));
                let global_index = table.n_columns_f_air() + lookup_ef.values * DIMENSION + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, value_eval);
                offset += 1 << log_n_rows;
            }
        }
        columns_values.insert(table, table_values);
    }

    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &point_gkr); // to compensate for the final padding: XYZ111111...1
    if retrieved_numerators_value != numerators_value {
        panic!()
    }
    if retrieved_denominators_value != denominators_value {
        panic!()
    }

    Ok(GenericLogupStatements {
        memory_and_acc_point,
        value_memory,
        value_memory_acc,
        bytecode_and_acc_point,
        value_bytecode_acc,
        bus_numerators_values,
        bus_denominators_values,
        points,
        columns_values,
        total_n_vars,
    })
}

fn offset_for_table(table: &Table, log_n_rows: usize) -> usize {
    let num_cols =
        table.lookups_f().iter().map(|l| l.values.len()).sum::<usize>() + table.lookups_ef().len() * DIMENSION + 1; // +1 for the bus
    num_cols << log_n_rows
}

fn compute_total_n_vars(log_memory: usize, log_bytecode: usize, tables_heights: &BTreeMap<Table, VarCount>) -> usize {
    let max_table_height = 1 << tables_heights.values().copied().max().unwrap();
    let total_len = (1 << log_memory)
        + (1 << log_bytecode).max(max_table_height) + (1 << tables_heights[&Table::execution()]) // bytecode
        + tables_heights
            .iter()
            .map(|(table, log_n_rows)| offset_for_table(table, *log_n_rows))
            .sum::<usize>();
    log2_ceil_usize(total_len)
}
