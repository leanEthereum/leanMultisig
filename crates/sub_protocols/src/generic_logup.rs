use lookup::prove_gkr_quotient;
use lookup::verify_gkr_quotient;
use multilinear_toolkit::prelude::*;
use utils::VecOrSlice;
use utils::from_end;
use utils::mle_of_01234567_etc;
use utils::to_big_endian_in_field;
use utils::{FSProver, assert_eq_many};

#[derive(Debug)]
pub struct GeneralizedLogupProver;

#[derive(Debug, PartialEq)]
pub struct GeneralizedLogupStatements<EF> {
    // lookup into memory
    pub on_table: Evaluation<EF>,
    pub on_acc: Evaluation<EF>,
    pub on_indexes: Vec<Evaluation<EF>>,
    pub on_values: Vec<Vec<Evaluation<EF>>>,
    // buses
    pub on_bus_numerators: Vec<Evaluation<EF>>,
    pub on_bus_denominators: Vec<Evaluation<EF>>,
}

#[derive(Debug)]
enum Dim {
    Table {
        n_vars: usize,
    },
    TableLookupGroup {
        group_index: usize,
        n_vars: usize,
        n_cols: usize,
    },
    Bus {
        n_vars: usize,
        index: usize,
    },
}

impl Dim {
    fn n_vars(&self) -> usize {
        match self {
            Dim::Table { n_vars } | Dim::TableLookupGroup { n_vars, .. } | Dim::Bus { n_vars, .. } => *n_vars,
        }
    }
    fn n_cols(&self) -> usize {
        match self {
            Dim::Table { .. } | Dim::Bus { .. } => 1,
            Dim::TableLookupGroup { n_cols, .. } => *n_cols,
        }
    }
}

fn get_sorted_dims(
    log_heights: &[usize],
    n_cols_per_group: &[usize],
    table_log_len: usize,
    bus_n_vars: &[usize],
) -> Vec<Dim> {
    let mut all_dims = vec![];
    for (index, (&n_vars, &n_cols)) in log_heights.iter().zip(n_cols_per_group).enumerate() {
        all_dims.push(Dim::TableLookupGroup {
            group_index: index,
            n_vars,
            n_cols,
        });
    }
    for (index, &n_vars) in bus_n_vars.iter().enumerate() {
        all_dims.push(Dim::Bus { n_vars, index });
    }
    all_dims.push(Dim::Table { n_vars: table_log_len });
    all_dims.sort_by_key(|d| std::cmp::Reverse(d.n_vars()));
    all_dims
}

impl GeneralizedLogupProver {
    #[allow(clippy::too_many_arguments)]
    pub fn run<EF: ExtensionField<PF<EF>>>(
        prover_state: &mut FSProver<EF, impl FSChallenger<EF>>,

        // parmeters for lookup into memory
        table: &[PF<EF>], // table[0] is assumed to be zero
        acc: &[PF<EF>],
        index_columns: Vec<&[PF<EF>]>,
        value_columns: Vec<Vec<VecOrSlice<'_, PF<EF>>>>, // value_columns[i][j] = (index_columns[i] + j)*table (using the notation of https://eprint.iacr.org/2025/946)

        // parameters for "buses" = information flow between different tables
        bus_numerators: Vec<&[PF<EF>]>,
        bus_denominators: Vec<&[EF]>,
        univariate_skips: usize,
    ) -> GeneralizedLogupStatements<EF> {
        assert!(table[0].is_zero());
        assert!(table.len().is_power_of_two());
        assert_eq!(table.len(), acc.len());
        assert_eq_many!(index_columns.len(), value_columns.len());
        assert_eq!(bus_numerators.len(), bus_denominators.len());
        bus_numerators
            .iter()
            .zip(bus_denominators.iter())
            .for_each(|(&sel, &data)| {
                assert_eq!(sel.len(), data.len());
            });

        let bus_n_vars = bus_numerators
            .iter()
            .map(|sel| log2_strict_usize(sel.len()))
            .collect::<Vec<usize>>();

        let n_groups = value_columns.len();
        let n_cols_per_group = value_columns.iter().map(|cols| cols.len()).collect::<Vec<usize>>();

        let log_heights = index_columns
            .iter()
            .map(|col| log2_strict_usize(col.len()))
            .collect::<Vec<usize>>();

        let all_dims = get_sorted_dims(
            &log_heights,
            &n_cols_per_group,
            log2_strict_usize(table.len()),
            &bus_n_vars,
        );
        let total_len = all_dims.iter().map(|d| d.n_cols() << d.n_vars()).sum::<usize>();
        let total_n_vars = log2_ceil_usize(total_len);
        tracing::info!("Logup data: {} = 2^{:.2}", total_len, (total_len as f64).log2());

        // logup (GKR)
        let c = prover_state.sample();
        let alpha = prover_state.sample();

        // challenge to separate the logup claims to the bus claims
        let beta = prover_state.sample();

        let mut numerators = EF::zero_vec(1 << total_n_vars);
        let mut denominators = EF::zero_vec(1 << total_n_vars);

        let mut offset = 0;
        for dim in &all_dims {
            match dim {
                Dim::TableLookupGroup { group_index, .. } => {
                    numerators[offset..][..dim.n_cols() << dim.n_vars()]
                        .par_iter_mut()
                        .for_each(|num| {
                            *num = EF::ONE;
                        }); // TODO embedding overhead
                    denominators[offset..][..dim.n_cols() << dim.n_vars()]
                        .par_chunks_exact_mut(1 << dim.n_vars())
                        .enumerate()
                        .for_each(|(i, denom_chunk)| {
                            let i_field = PF::<EF>::from_usize(i);
                            denom_chunk.par_iter_mut().enumerate().for_each(|(j, denom)| {
                                *denom = c
                                    - (alpha * (index_columns[*group_index][j] + i_field)
                                        + value_columns[*group_index][i].as_slice()[j]);
                            });
                        });
                }
                Dim::Table { .. } => {
                    // table

                    // TODO embedding overhead
                    numerators[offset..]
                        .par_iter_mut()
                        .zip(acc)
                        .for_each(|(num, a)| *num = EF::from(-*a)); // Note the negative sign here
                    denominators[offset..]
                        .par_iter_mut()
                        .zip(table.par_iter().enumerate())
                        .for_each(|(denom, (i, &t))| *denom = c - (alpha * PF::<EF>::from_usize(i) + t));
                }
                Dim::Bus { index, .. } => {
                    numerators[offset..]
                        .par_iter_mut()
                        .zip(bus_numerators[*index])
                        .for_each(|(num, sel)| *num = beta * *sel); // TODO often sel = ONE, so this is innefficient
                    denominators[offset..]
                        .par_iter_mut()
                        .zip(bus_denominators[*index].par_iter())
                        .for_each(|(denom, &data)| *denom = data);
                }
            }
            offset += dim.n_cols() << dim.n_vars();
        }
        denominators[offset..].par_iter_mut().for_each(|d| *d = EF::ONE); // padding

        let numerators_packed = MleRef::Extension(&numerators).pack();
        let denominators_packed = MleRef::Extension(&denominators).pack();

        let (sum, claim_point_gkr, numerators_value, denominators_value) = prove_gkr_quotient::<_, 2>(
            prover_state,
            &MleGroupRef::merge(&[&numerators_packed.by_ref(), &denominators_packed.by_ref()]),
        );

        let _ = (numerators_value, denominators_value); // TODO use it to avoid some computation below

        // sanity check
        assert_eq!(sum, EF::ZERO);

        let mut statement_on_table = None;
        let mut statement_on_acc = None;
        let mut statement_on_indexes = vec![None; n_groups];
        let mut statement_on_values = vec![vec![]; n_groups];

        // bus statements
        let mut bus_numerators_statements = vec![None; bus_numerators.len()];
        let mut bus_denominators_statements = vec![None; bus_denominators.len()];

        for dim in &all_dims {
            let inner_point = MultilinearPoint(from_end(&claim_point_gkr, dim.n_vars()).to_vec());

            match dim {
                Dim::TableLookupGroup { group_index, .. } => {
                    let index_eval = index_columns[*group_index].evaluate(&inner_point);
                    prover_state.add_extension_scalar(index_eval);
                    statement_on_indexes[*group_index] = Some(Evaluation::new(inner_point.clone(), index_eval));
                    for col_index in 0..dim.n_cols() {
                        let value_eval = value_columns[*group_index][col_index].as_slice().evaluate(&inner_point);
                        prover_state.add_extension_scalar(value_eval);
                        statement_on_values[*group_index].push(Evaluation::new(inner_point.clone(), value_eval));
                    }
                }
                Dim::Table { .. } => {
                    // table

                    let value_acc = acc.evaluate(&inner_point);
                    prover_state.add_extension_scalar(value_acc);
                    statement_on_acc = Some(Evaluation::new(inner_point.clone(), value_acc));

                    let value_table = table.evaluate(&inner_point);
                    prover_state.add_extension_scalar(value_table);
                    statement_on_table = Some(Evaluation::new(inner_point, value_table));
                }
                Dim::Bus { index, .. } => {
                    let inner_inner_point = MultilinearPoint(inner_point[univariate_skips..].to_vec());
                    let evals_on_selector = bus_numerators[*index]
                        .par_chunks_exact(bus_numerators[*index].len() >> univariate_skips)
                        .map(|chunk| chunk.evaluate(&inner_inner_point))
                        .collect::<Vec<EF>>();
                    prover_state.add_extension_scalars(&evals_on_selector);
                    bus_numerators_statements[*index] =
                        Some(MultiEvaluation::new(inner_inner_point.clone(), evals_on_selector));

                    let eval_on_data = bus_denominators[*index]
                        .par_chunks_exact(bus_denominators[*index].len() >> univariate_skips)
                        .map(|chunk| chunk.evaluate(&inner_inner_point))
                        .collect::<Vec<EF>>();
                    prover_state.add_extension_scalars(&eval_on_data);
                    bus_denominators_statements[*index] = Some(MultiEvaluation::new(inner_inner_point, eval_on_data));
                }
            }
        }

        let gamma = prover_state.sample();

        let unvariate_selectors_evals = univariate_selectors::<PF<EF>>(univariate_skips)
            .iter()
            .map(|p| p.evaluate(gamma))
            .collect::<Vec<EF>>();

        GeneralizedLogupStatements {
            on_table: statement_on_table.unwrap(),
            on_acc: statement_on_acc.unwrap(),
            on_indexes: statement_on_indexes.into_iter().map(Option::unwrap).collect(),
            on_values: statement_on_values,
            on_bus_numerators: bus_numerators_statements
                .into_iter()
                .map(|s| combine_inner_bus_statements(s, gamma, &unvariate_selectors_evals))
                .collect::<Vec<_>>(),
            on_bus_denominators: bus_denominators_statements
                .into_iter()
                .map(|s| combine_inner_bus_statements(s, gamma, &unvariate_selectors_evals))
                .collect::<Vec<_>>(),
        }
    }
}

fn combine_inner_bus_statements<EF: ExtensionField<PF<EF>>>(
    s: Option<MultiEvaluation<EF>>,
    gamma: EF,
    unvariate_selectors_evals: &[EF],
) -> Evaluation<EF> {
    let s = s.unwrap();
    let mut new_point = s.point.clone();
    new_point.insert(0, gamma);
    let new_value = dot_product(unvariate_selectors_evals.iter().copied(), s.values.into_iter());
    Evaluation::new(new_point, new_value)
}

#[derive(Debug)]
pub struct GeneralizedLogupVerifier;

impl GeneralizedLogupVerifier {
    pub fn run<EF: ExtensionField<PF<EF>>>(
        verifier_state: &mut FSVerifier<EF, impl FSChallenger<EF>>,
        table_log_len: usize,
        log_heights: Vec<usize>,
        n_cols_per_group: Vec<usize>,
        bus_n_vars: Vec<usize>,
        univariate_skips: usize,
    ) -> ProofResult<GeneralizedLogupStatements<EF>> {
        let all_dims = get_sorted_dims(&log_heights, &n_cols_per_group, table_log_len, &bus_n_vars);
        let total_len = all_dims.iter().map(|d| d.n_cols() << d.n_vars()).sum::<usize>();
        let total_n_vars = log2_ceil_usize(total_len);

        // logup (GKR)
        let c = verifier_state.sample();
        let alpha = verifier_state.sample();

        // challenge to separate the logup claims to the bus claims
        let beta = verifier_state.sample();

        let (sum, claim_point_gkr, numerators_value, denominators_value) =
            verify_gkr_quotient::<_, 2>(verifier_state, total_n_vars)?;

        if sum != EF::ZERO {
            return Err(ProofError::InvalidProof);
        }

        let mut retrieved_numerators_value = EF::ZERO;
        let mut retrieved_denominators_value = EF::ZERO;

        let mut offset = 0;
        let mut statement_on_table = None;
        let mut statement_on_acc = None;
        let mut statement_on_indexes = vec![None; n_cols_per_group.len()];
        let mut statement_on_values = vec![vec![]; n_cols_per_group.len()];
        let mut bus_numerators_statements = vec![None; bus_n_vars.len()];
        let mut bus_denominators_statements = vec![None; bus_n_vars.len()];

        for dim in &all_dims {
            let inner_point = MultilinearPoint(from_end(&claim_point_gkr, dim.n_vars()).to_vec());
            let n_missing_vars = total_n_vars - dim.n_vars();
            let missing_point = MultilinearPoint(claim_point_gkr[..n_missing_vars].to_vec());

            match dim {
                Dim::TableLookupGroup { group_index, .. } => {
                    let index_eval = verifier_state.next_extension_scalar()?;
                    statement_on_indexes[*group_index] = Some(Evaluation::new(inner_point.clone(), index_eval));

                    for col_index in 0..dim.n_cols() {
                        let value_eval = verifier_state.next_extension_scalar()?;
                        statement_on_values[*group_index].push(Evaluation::new(inner_point.clone(), value_eval));

                        let pos = offset + (col_index << dim.n_vars());
                        let bits = to_big_endian_in_field::<EF>(pos >> dim.n_vars(), n_missing_vars);
                        let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                        retrieved_numerators_value += pref;
                        retrieved_denominators_value +=
                            pref * (c - (alpha * (index_eval + PF::<EF>::from_usize(col_index)) + value_eval));
                    }
                }
                Dim::Table { .. } => {
                    // table
                    let bits = to_big_endian_in_field::<EF>(offset >> dim.n_vars(), n_missing_vars);
                    let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);

                    let value_acc = verifier_state.next_extension_scalar()?;
                    statement_on_acc = Some(Evaluation::new(inner_point.clone(), value_acc));
                    retrieved_numerators_value -= pref * value_acc;

                    let value_table = verifier_state.next_extension_scalar()?;
                    statement_on_table = Some(Evaluation::new(inner_point.clone(), value_table));
                    retrieved_denominators_value +=
                        pref * (c - (alpha * mle_of_01234567_etc(&inner_point) + value_table));
                }
                Dim::Bus { index, .. } => {
                    let missing_inner_point = MultilinearPoint(inner_point[..univariate_skips].to_vec());
                    let inner_inner_point = MultilinearPoint(inner_point[univariate_skips..].to_vec());
                    let evals_on_numerators = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;
                    bus_numerators_statements[*index] = Some(MultiEvaluation::new(
                        inner_inner_point.clone(),
                        evals_on_numerators.clone(),
                    ));
                    let bits = to_big_endian_in_field::<EF>(offset >> dim.n_vars(), n_missing_vars);
                    let pref = MultilinearPoint(bits).eq_poly_outside(&missing_point);
                    retrieved_numerators_value += pref * beta * evals_on_numerators.evaluate(&missing_inner_point);

                    let evals_on_denominators = verifier_state.next_extension_scalars_vec(1 << univariate_skips)?;
                    bus_denominators_statements[*index] =
                        Some(MultiEvaluation::new(inner_inner_point.clone(), evals_on_denominators.clone()));
                    retrieved_denominators_value += pref * evals_on_denominators.evaluate(&missing_inner_point);
                }
            }
            offset += dim.n_cols() << dim.n_vars();
        }

        retrieved_denominators_value += mle_of_zeros_then_ones(offset, &claim_point_gkr); // to compensate for the final padding: XYZ111111...1
        if retrieved_numerators_value != numerators_value {
            return Err(ProofError::InvalidProof);
        }
        if retrieved_denominators_value != denominators_value {
            return Err(ProofError::InvalidProof);
        }

        let gamma = verifier_state.sample();

        let unvariate_selectors_evals = univariate_selectors::<PF<EF>>(univariate_skips)
            .iter()
            .map(|p| p.evaluate(gamma))
            .collect::<Vec<EF>>();

        Ok(GeneralizedLogupStatements {
            on_table: statement_on_table.unwrap(),
            on_acc: statement_on_acc.unwrap(),
            on_indexes: statement_on_indexes.into_iter().map(Option::unwrap).collect(),
            on_values: statement_on_values,
            on_bus_numerators: bus_numerators_statements
                .into_iter()
                .map(|s| combine_inner_bus_statements(s, gamma, &unvariate_selectors_evals))
                .collect::<Vec<_>>(),
            on_bus_denominators: bus_denominators_statements
                .into_iter()
                .map(|s| combine_inner_bus_statements(s, gamma, &unvariate_selectors_evals))
                .collect::<Vec<_>>(),
        })
    }
}
