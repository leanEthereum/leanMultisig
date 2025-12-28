use crate::{prove_gkr_quotient, verify_gkr_quotient};
use lean_vm::BusDirection;
use lean_vm::BusTable;
use lean_vm::ColIndex;
use lean_vm::DIMENSION;
use lean_vm::EF;
use lean_vm::F;
use lean_vm::Table;
use lean_vm::TableT;
use lean_vm::TableTrace;
use lean_vm::max_bus_width;
use lean_vm::sort_tables_by_height;
use multilinear_toolkit::prelude::*;
use std::collections::BTreeMap;
use utils::MEMORY_TABLE_INDEX;
use utils::VarCount;
use utils::VecOrSlice;
use utils::finger_print;
use utils::from_end;
use utils::mle_of_01234567_etc;
use utils::to_big_endian_in_field;
use utils::transpose_slice_to_basis_coefficients;

#[derive(Debug, PartialEq, Hash, Clone)]
pub struct GenericLogupStatements {
    pub memory_acc_point: MultilinearPoint<EF>,
    pub value_memory: EF,
    pub value_acc: EF,
    pub bus_points: BTreeMap<Table, MultilinearPoint<EF>>,
    pub bus_numerators_values: BTreeMap<Table, EF>,
    pub bus_denominators_values: BTreeMap<Table, EF>,
    pub columns_points: BTreeMap<Table, MultilinearPoint<EF>>,
    pub columns_values: BTreeMap<Table, BTreeMap<ColIndex, EF>>,
    // Used in recursion
    pub total_n_vars: usize,
}

#[allow(clippy::too_many_arguments)]
pub fn prove_generic_logup(
    prover_state: &mut impl FSProver<EF>,
    c: EF,
    alpha: EF,
    memory: &[F],
    acc: &[F],
    traces: &BTreeMap<Table, TableTrace>,
    univariate_skips: usize,
) -> GenericLogupStatements {
    assert!(memory[0].is_zero());
    assert!(memory.len().is_power_of_two());
    assert_eq!(memory.len(), acc.len());
    assert!(memory.len() >= traces.values().map(|t| 1 << t.log_n_rows).max().unwrap());

    let tables_heights = traces.iter().map(|(table, trace)| (*table, trace.log_n_rows)).collect();
    let tables_heights_sorted = sort_tables_by_height(&tables_heights);

    let total_n_vars = compute_total_n_vars(
        log2_strict_usize(memory.len()),
        &tables_heights_sorted.iter().cloned().collect(),
    );
    let mut numerators = EF::zero_vec(1 << total_n_vars);
    let mut denominators = EF::zero_vec(1 << total_n_vars);

    let alpha_powers = alpha.powers().collect_n(max_bus_width());

    // Memory: ...
    numerators[..memory.len()]
        .par_iter_mut()
        .zip(acc) // TODO embedding overhead
        .for_each(|(num, a)| *num = EF::from(-*a)); // Note the negative sign here 
    denominators[..memory.len()]
        .par_iter_mut()
        .zip(memory.par_iter().enumerate())
        .for_each(|(denom, (i, &mem_value))| {
            *denom = c - finger_print(
                F::from_usize(MEMORY_TABLE_INDEX),
                &[F::from_usize(i), mem_value],
                &alpha_powers,
            )
        });

    // ... Rest of the tables:
    let mut offset = memory.len();
    for (table, _) in &tables_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

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
                        &alpha_powers,
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
                                c - finger_print(F::from_usize(MEMORY_TABLE_INDEX), &[index, mem_value], &alpha_powers)
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
    let memory_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log2_strict_usize(memory.len())).to_vec());
    let value_acc = acc.evaluate(&memory_acc_point);
    prover_state.add_extension_scalar(value_acc);

    let value_memory = memory.evaluate(&memory_acc_point);
    prover_state.add_extension_scalar(value_memory);

    // ... Rest of the tables:
    let mut bus_points = BTreeMap::new();
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_points = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    let mut offset = memory.len();
    for (table, _) in &tables_heights_sorted {
        let trace = &traces[table];
        let log_n_rows = trace.log_n_rows;

        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        columns_points.insert(*table, inner_point.clone());

        // I] Bus (data flow between tables)

        let inner_inner_point = MultilinearPoint(inner_point[univariate_skips..].to_vec());
        let evals_on_selector = trace.base[table.bus().selector]
            .par_chunks_exact(1 << (log_n_rows - univariate_skips))
            .map(|chunk| chunk.evaluate(&inner_inner_point) * table.bus().direction.to_field_flag())
            .collect::<Vec<EF>>();
        prover_state.add_extension_scalars(&evals_on_selector);

        let eval_on_data = denominators[offset..][..1 << log_n_rows]
            .par_chunks_exact(1 << (log_n_rows - univariate_skips))
            .map(|chunk| chunk.evaluate(&inner_inner_point))
            .collect::<Vec<EF>>();
        prover_state.add_extension_scalars(&eval_on_data);

        let gamma = prover_state.sample();
        prover_state.duplexing();

        let unvariate_selectors_evals = univariate_selectors::<PF<EF>>(univariate_skips)
            .iter()
            .map(|p| p.evaluate(gamma))
            .collect::<Vec<EF>>();

        bus_points.insert(*table, {
            let mut point = inner_inner_point.clone();
            point.insert(0, gamma);
            point
        });
        bus_numerators_values.insert(
            *table,
            dot_product(
                unvariate_selectors_evals.iter().copied(),
                evals_on_selector.iter().copied(),
            ),
        );
        bus_denominators_values.insert(
            *table,
            dot_product(unvariate_selectors_evals.iter().copied(), eval_on_data.iter().copied()),
        );

        // II] Lookup into memory

        let mut table_values = BTreeMap::<ColIndex, EF>::new();
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
                let global_index = table.n_commited_columns_f() + lookup_ef.values * DIMENSION + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, value_eval);
            }
        }
        columns_points.insert(*table, inner_point);
        columns_values.insert(*table, table_values);

        offset += offset_for_table(table, log_n_rows);
    }

    GenericLogupStatements {
        memory_acc_point,
        value_memory,
        value_acc,
        bus_points,
        bus_numerators_values,
        bus_denominators_values,
        columns_points,
        columns_values,
        total_n_vars,
    }
}

#[allow(clippy::too_many_arguments)]
pub fn verify_generic_logup(
    verifier_state: &mut impl FSVerifier<EF>,
    c: EF,
    alpha: EF,
    log_memory: usize,
    table_log_n_rows: &BTreeMap<Table, VarCount>,
    univariate_skips: usize,
) -> ProofResult<GenericLogupStatements> {
    let tables_heights_sorted = sort_tables_by_height(table_log_n_rows);

    let total_n_vars = compute_total_n_vars(log_memory, &tables_heights_sorted.iter().cloned().collect());

    let (sum, claim_point_gkr, numerators_value, denominators_value) =
        verify_gkr_quotient(verifier_state, total_n_vars)?;

    if sum != EF::ZERO {
        return Err(ProofError::InvalidProof);
    }

    let alpha_powers = alpha.powers().collect_n(max_bus_width());

    let mut retrieved_numerators_value = EF::ZERO;
    let mut retrieved_denominators_value = EF::ZERO;

    // Memory ...
    let memory_acc_point = MultilinearPoint(from_end(&claim_point_gkr, log_memory).to_vec());
    let bits = to_big_endian_in_field::<EF>(0, total_n_vars - log_memory);
    let pref = MultilinearPoint(bits)
        .eq_poly_outside(&MultilinearPoint(claim_point_gkr[..total_n_vars - log_memory].to_vec()));

    let value_acc = verifier_state.next_extension_scalar()?;
    retrieved_numerators_value -= pref * value_acc;

    let value_memory = verifier_state.next_extension_scalar()?;
    let value_index = mle_of_01234567_etc(&memory_acc_point);
    retrieved_denominators_value += pref
        * (c - finger_print(
            F::from_usize(MEMORY_TABLE_INDEX),
            &[value_index, value_memory],
            &alpha_powers,
        ));

    // ... Rest of the tables:
    let mut bus_points = BTreeMap::new();
    let mut bus_numerators_values = BTreeMap::new();
    let mut bus_denominators_values = BTreeMap::new();
    let mut columns_points = BTreeMap::new();
    let mut columns_values = BTreeMap::new();
    let mut offset = 1 << log_memory;
    for &(table, log_n_rows) in &tables_heights_sorted {
        let n_missing_vars = total_n_vars - log_n_rows;
        let inner_point = MultilinearPoint(from_end(&claim_point_gkr, log_n_rows).to_vec());
        let missing_point = MultilinearPoint(claim_point_gkr[..n_missing_vars].to_vec());
        let missing_inner_point = MultilinearPoint(inner_point[..univariate_skips].to_vec());

        columns_points.insert(table, inner_point.clone());

        // I] Bus (data flow between tables)

        let inner_inner_point = MultilinearPoint(inner_point[univariate_skips..].to_vec());
        let evals_on_selector = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;

        let bits = to_big_endian_in_field::<EF>(offset >> log_n_rows, n_missing_vars);
        let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
        retrieved_numerators_value += pref * evals_on_selector.evaluate(&missing_inner_point);

        let eval_on_data = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;
        retrieved_denominators_value += pref * eval_on_data.evaluate(&missing_inner_point);

        let gamma = verifier_state.sample();
        verifier_state.duplexing();

        let unvariate_selectors_evals = univariate_selectors::<PF<EF>>(univariate_skips)
            .iter()
            .map(|p| p.evaluate(gamma))
            .collect::<Vec<EF>>();

        bus_points.insert(table, {
            let mut point = inner_inner_point.clone();
            point.insert(0, gamma);
            point
        });
        bus_numerators_values.insert(
            table,
            dot_product(
                unvariate_selectors_evals.iter().copied(),
                evals_on_selector.iter().copied(),
            ),
        );
        bus_denominators_values.insert(
            table,
            dot_product(unvariate_selectors_evals.iter().copied(), eval_on_data.iter().copied()),
        );

        offset += 1 << log_n_rows;

        // II] Lookup into memory

        let mut table_values = BTreeMap::<ColIndex, EF>::new();
        for lookup_f in table.lookups_f() {
            let index_eval = verifier_state.next_extension_scalar()?;
            assert!(!table_values.contains_key(&lookup_f.index));
            table_values.insert(lookup_f.index, index_eval);

            for (i, col_index) in lookup_f.values.iter().enumerate() {
                let value_eval = verifier_state.next_extension_scalar()?;
                assert!(!table_values.contains_key(col_index));
                table_values.insert(*col_index, value_eval);

                let pos = offset + (i << log_n_rows);
                let bits = to_big_endian_in_field::<EF>(pos >> log_n_rows, n_missing_vars);
                let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                retrieved_numerators_value += pref;
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        F::from_usize(MEMORY_TABLE_INDEX),
                        &[index_eval + F::from_usize(i), value_eval],
                        &alpha_powers,
                    ));
            }
            offset += lookup_f.values.len() << log_n_rows;
        }

        for lookup_ef in table.lookups_ef() {
            let index_eval = verifier_state.next_extension_scalar()?;
            assert_eq!(table_values.get(&lookup_ef.index).unwrap_or(&index_eval), &index_eval);
            table_values.insert(lookup_ef.index, index_eval);

            for i in 0..DIMENSION {
                let value_eval = verifier_state.next_extension_scalar()?;

                let pos = offset + (i << log_n_rows);
                let bits = to_big_endian_in_field::<EF>(pos >> log_n_rows, n_missing_vars);
                let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                retrieved_numerators_value += pref;
                retrieved_denominators_value += pref
                    * (c - finger_print(
                        F::from_usize(MEMORY_TABLE_INDEX),
                        &[index_eval + F::from_usize(i), value_eval],
                        &alpha_powers,
                    ));
                let global_index = table.n_commited_columns_f() + lookup_ef.values * DIMENSION + i;
                assert!(!table_values.contains_key(&global_index));
                table_values.insert(global_index, value_eval);
            }
            offset += DIMENSION << log_n_rows;
        }
        columns_values.insert(table, table_values);
    }

    retrieved_denominators_value += mle_of_zeros_then_ones(offset, &claim_point_gkr); // to compensate for the final padding: XYZ111111...1
    if retrieved_numerators_value != numerators_value {
        return Err(ProofError::InvalidProof);
    }
    if retrieved_denominators_value != denominators_value {
        return Err(ProofError::InvalidProof);
    }

    Ok(GenericLogupStatements {
        memory_acc_point,
        value_memory,
        value_acc,
        bus_points,
        bus_numerators_values,
        bus_denominators_values,
        columns_points,
        columns_values,
        total_n_vars,
    })
}

fn offset_for_table(table: &Table, log_n_rows: usize) -> usize {
    let num_cols =
        table.lookups_f().iter().map(|l| l.values.len()).sum::<usize>() + table.lookups_ef().len() * DIMENSION + 1; // +1 for the bus
    num_cols << log_n_rows
}

fn compute_total_n_vars(log_memory: usize, tables_heights: &BTreeMap<Table, VarCount>) -> usize {
    let total_len = (1 << log_memory)
        + tables_heights
            .iter()
            .map(|(table, log_n_rows)| offset_for_table(table, *log_n_rows))
            .sum::<usize>();
    log2_ceil_usize(total_len)
}
