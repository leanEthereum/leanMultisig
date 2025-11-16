use std::{
    any::TypeId,
    mem::{transmute, transmute_copy},
};

use multilinear_toolkit::prelude::*;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_koala_bear::{KoalaBear, QuinticExtensionFieldKB};
use p3_uni_stark::SymbolicExpression;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::{build_prover_state, build_verifier_state};

use crate::{prove::prove_air, table::AirTable, verify::verify_air};

const UNIVARIATE_SKIPS: usize = 3;

const N_COLS_WITHOUT_SHIFT: usize = 2;

type F = KoalaBear;
type EF = QuinticExtensionFieldKB;

struct ExampleStructuredAir<
    const N_COLUMNS: usize,
    const N_PREPROCESSED_COLUMNS: usize,
    const VIRTUAL_COLUMN: bool,
>;

impl<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize, const VIRTUAL_COLUMN: bool>
    SumcheckComputationForAir
    for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS, VIRTUAL_COLUMN>
{
}

impl<F, const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize, const VIRTUAL_COLUMN: bool>
    BaseAir<F> for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS, VIRTUAL_COLUMN>
{
    fn width(&self) -> usize {
        N_COLUMNS
    }
    fn degree(&self) -> usize {
        N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT
    }
    fn columns_with_shift(&self) -> Vec<usize> {
        [
            (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT).collect::<Vec<_>>(),
            (N_PREPROCESSED_COLUMNS..N_COLUMNS).collect::<Vec<_>>(),
        ]
        .concat()
    }
}

impl<
    AB: AirBuilder,
    const N_COLUMNS: usize,
    const N_PREPROCESSED_COLUMNS: usize,
    const VIRTUAL_COLUMN: bool,
> Air<AB> for ExampleStructuredAir<N_COLUMNS, N_PREPROCESSED_COLUMNS, VIRTUAL_COLUMN>
where
    AB::Var: 'static,
    AB::Expr: 'static,
    AB::FinalOutput: 'static,
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main[..N_COLUMNS].to_vec();
        let down = main[N_COLUMNS..].to_vec();
        assert_eq!(down.len(), N_COLUMNS - N_COLS_WITHOUT_SHIFT);

        if VIRTUAL_COLUMN {
            // virtual column = col_0 * col_1 + col_2
            builder.add_custom(<Self as Air<AB>>::eval_custom(
                self,
                &[
                    up[0].clone().into(),
                    up[1].clone().into(),
                    up[2].clone().into(),
                ],
            ));
        }

        for j in N_PREPROCESSED_COLUMNS..N_COLUMNS {
            builder.assert_eq(
                down[j - N_COLS_WITHOUT_SHIFT].clone(),
                up[j].clone()
                    + AB::F::from_usize(j)
                    + (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT)
                        .map(|k| AB::Expr::from(down[k].clone()))
                        .product::<AB::Expr>(),
            );
        }
    }

    fn eval_custom(&self, inputs: &[<AB as AirBuilder>::Expr]) -> <AB as AirBuilder>::FinalOutput {
        assert_eq!(inputs.len(), 3);
        let type_id_final_output = TypeId::of::<<AB as AirBuilder>::FinalOutput>();
        let type_id_expr = TypeId::of::<<AB as AirBuilder>::Expr>();
        let type_id_f = TypeId::of::<F>();
        let type_id_ef = TypeId::of::<EF>();
        let type_id_f_packing = TypeId::of::<PFPacking<EF>>();
        let type_id_ef_packing = TypeId::of::<EFPacking<EF>>();

        if type_id_expr == type_id_f && type_id_final_output == type_id_ef {
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[F]>(inputs) };
            let res = EF::from(inputs[0] * inputs[1] + inputs[2]);
            unsafe { transmute_copy::<EF, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_ef && type_id_final_output == type_id_ef {
            let inputs = unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EF]>(inputs) };
            let res = inputs[0] * inputs[1] + inputs[2];
            unsafe { transmute_copy::<EF, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_ef_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[EFPacking<EF>]>(inputs) };
            let res = inputs[0] * inputs[1] + inputs[2];
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else if type_id_expr == type_id_f_packing {
            assert_eq!(type_id_final_output, type_id_ef_packing);
            let inputs =
                unsafe { transmute::<&[<AB as AirBuilder>::Expr], &[PFPacking<EF>]>(inputs) };
            let res = EFPacking::<EF>::from(inputs[0] * inputs[1] + inputs[2]);
            unsafe { transmute_copy::<EFPacking<EF>, <AB as AirBuilder>::FinalOutput>(&res) }
        } else {
            assert_eq!(type_id_expr, TypeId::of::<SymbolicExpression<F>>());
            unsafe { transmute_copy(&SymbolicExpression::<F>::default()) }
        }
    }
}

fn generate_structured_trace<const N_COLUMNS: usize, const N_PREPROCESSED_COLUMNS: usize>(
    n_rows: usize,
) -> Vec<Vec<F>> {
    let mut trace = vec![];
    let mut rng = StdRng::seed_from_u64(0);
    for _ in 0..N_PREPROCESSED_COLUMNS {
        trace.push((0..n_rows).map(|_| rng.random()).collect::<Vec<F>>());
    }
    let mut witness_cols = vec![vec![F::ZERO]; N_COLUMNS - N_PREPROCESSED_COLUMNS];
    for i in 1..n_rows {
        for (j, witness_col) in witness_cols
            .iter_mut()
            .enumerate()
            .take(N_COLUMNS - N_PREPROCESSED_COLUMNS)
        {
            let witness_cols_j_i_min_1 = witness_col[i - 1];
            witness_col.push(
                witness_cols_j_i_min_1
                    + F::from_usize(j + N_PREPROCESSED_COLUMNS)
                    + (0..N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT)
                        .map(|k| trace[k][i])
                        .product::<F>(),
            );
        }
    }
    trace.extend(witness_cols);
    trace
}

#[test]
fn test_air() {
    test_air_helper::<true>();
    test_air_helper::<false>();
}

fn test_air_helper<const VIRTUAL_COLUMN: bool>() {
    const N_COLUMNS: usize = 17;
    const N_PREPROCESSED_COLUMNS: usize = 5;
    const _: () = assert!(N_PREPROCESSED_COLUMNS > N_COLS_WITHOUT_SHIFT);
    let log_n_rows = 12;
    let n_rows = 1 << log_n_rows;
    let mut prover_state = build_prover_state::<EF>();

    let columns_plus_one =
        generate_structured_trace::<N_COLUMNS, N_PREPROCESSED_COLUMNS>(n_rows + 1);
    let columns_ref = columns_plus_one
        .iter()
        .map(|col| &col[..n_rows])
        .collect::<Vec<_>>();
    let mut last_row = columns_plus_one
        .iter()
        .map(|col| col[n_rows])
        .collect::<Vec<_>>();
    last_row.drain(N_PREPROCESSED_COLUMNS - N_COLS_WITHOUT_SHIFT..N_PREPROCESSED_COLUMNS);
    let last_row_ef = last_row.iter().map(|&v| EF::from(v)).collect::<Vec<_>>();

    let virtual_column_statement_prover = if VIRTUAL_COLUMN {
        let virtual_column = columns_ref[0]
            .iter()
            .zip(columns_ref[1].iter())
            .zip(columns_ref[2].iter())
            .map(|((&a, &b), &c)| a * b + c)
            .collect::<Vec<_>>();
        let virtual_column_evaluation_point =
            MultilinearPoint(prover_state.sample_vec(log_n_rows + 1 - UNIVARIATE_SKIPS));
        let selectors = univariate_selectors(UNIVARIATE_SKIPS);
        let virtual_column_value = evaluate_univariate_multilinear::<_, _, _, true>(
            &virtual_column,
            &virtual_column_evaluation_point,
            &selectors,
            None,
        );
        prover_state.add_extension_scalar(virtual_column_value);

        Some(Evaluation::new(
            virtual_column_evaluation_point.0.clone(),
            virtual_column_value,
        ))
    } else {
        None
    };

    let table = AirTable::<EF, _>::new(ExampleStructuredAir::<
        N_COLUMNS,
        N_PREPROCESSED_COLUMNS,
        VIRTUAL_COLUMN,
    > {});

    table.check_trace_validity(&columns_ref, &last_row).unwrap();

    let (point_prover, evaluations_remaining_to_prove) = prove_air(
        &mut prover_state,
        &table,
        UNIVARIATE_SKIPS,
        &columns_ref,
        &last_row,
        virtual_column_statement_prover,
        true
    );
    let mut verifier_state = build_verifier_state(&prover_state);

    let virtual_column_statement_verifier = if VIRTUAL_COLUMN {
        let virtual_column_evaluation_point =
            MultilinearPoint(verifier_state.sample_vec(log_n_rows + 1 - UNIVARIATE_SKIPS));
        let virtual_column_value = verifier_state.next_extension_scalar().unwrap();
        Some(Evaluation::new(
            virtual_column_evaluation_point.0.clone(),
            virtual_column_value,
        ))
    } else {
        None
    };

    let (point_verifier, evaluations_remaining_to_verify) = verify_air(
        &mut verifier_state,
        &table,
        UNIVARIATE_SKIPS,
        log_n_rows,
        &last_row_ef,
        virtual_column_statement_verifier,
    )
    .unwrap();
    assert_eq!(point_prover, point_verifier);
    assert_eq!(
        &evaluations_remaining_to_prove,
        &evaluations_remaining_to_verify
    );
    for i in 0..N_COLUMNS {
        assert_eq!(
            columns_ref[i].evaluate(&point_prover),
            evaluations_remaining_to_verify[i]
        );
    }
}
