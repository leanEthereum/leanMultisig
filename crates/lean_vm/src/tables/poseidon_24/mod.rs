use p3_poseidon2::GenericPoseidon2LinearLayers;
use std::{any::TypeId, array};

use crate::{tables::poseidon_24::trace_gen::default_poseidon_24_row, *};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC24_EXTERNAL_FINAL, KOALABEAR_RC24_EXTERNAL_INITIAL,
    KOALABEAR_RC24_INTERNAL,
};
use utils::{ToUsize, poseidon24_permute};

mod test;
mod trace_gen;

pub use test::benchmark_prove_poseidon_24;
pub use trace_gen::fill_trace_poseidon_24;

pub(super) const WIDTH_24: usize = 24;
const HALF_INITIAL_FULL_ROUNDS: usize = KOALABEAR_RC24_EXTERNAL_INITIAL.len() / 2;
const PARTIAL_ROUNDS: usize = KOALABEAR_RC24_INTERNAL.len();
const HALF_FINAL_FULL_ROUNDS: usize = KOALABEAR_RC24_EXTERNAL_FINAL.len() / 2;

pub const POSEIDON_24_COL_FLAG: ColIndex = 0;
pub const POSEIDON_24_COL_INDEX_RES: ColIndex = 1;
pub const POSEIDON_24_COL_INDEX_RES_BIS: ColIndex = 2;
pub const POSEIDON_24_COL_INDEX_RES_BIS_BIS: ColIndex = 3;
pub const POSEIDON_24_COL_INDEX_A: ColIndex = 4;
pub const POSEIDON_24_COL_INDEX_A_BIS: ColIndex = 5;
pub const POSEIDON_24_COL_INDEX_B: ColIndex = 6;
pub const POSEIDON_24_COL_INPUT_START: ColIndex = 7;
const POSEIDON_24_COL_OUTPUT_START: ColIndex = num_cols_24() - 24;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon24Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon24Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon24"
    }

    fn identifier(&self) -> Table {
        Table::poseidon24()
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_A,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_A_BIS,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_B,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + 2 * VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_RES,
                values: array::from_fn(|i| POSEIDON_24_COL_OUTPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_RES_BIS,
                values: array::from_fn(|i| POSEIDON_24_COL_OUTPUT_START + VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_RES_BIS_BIS,
                values: array::from_fn(|i| POSEIDON_24_COL_OUTPUT_START + 2 * VECTOR_LEN + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        assert!(BUS);
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: POSEIDON_24_COL_FLAG,
            data: vec![
                POSEIDON_24_COL_INDEX_A,
                POSEIDON_24_COL_INDEX_B,
                POSEIDON_24_COL_INDEX_RES,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        default_poseidon_24_row()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        index_res: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(aux == 0);
        let trace = ctx.traces.get_mut(&self.identifier()).unwrap();

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), VECTOR_LEN * 2)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), VECTOR_LEN)?;

        let mut input = [F::ZERO; VECTOR_LEN * 3];
        input[..VECTOR_LEN * 2].copy_from_slice(&arg0);
        input[VECTOR_LEN * 2..].copy_from_slice(&arg1);

        let output = match ctx.poseidon24_precomputed.get(*ctx.n_poseidon24_precomputed_used) {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon24_precomputed_used += 1;
                precomputed.1
            }
            _ => poseidon24_permute(input),
        };

        ctx.memory.set_slice(index_res.to_usize(), &output)?;

        trace.base[POSEIDON_24_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_24_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_24_COL_INDEX_A_BIS].push(arg_a + F::from_usize(VECTOR_LEN));
        trace.base[POSEIDON_24_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_24_COL_INDEX_RES].push(index_res);
        trace.base[POSEIDON_24_COL_INDEX_RES_BIS].push(index_res + F::from_usize(VECTOR_LEN));
        trace.base[POSEIDON_24_COL_INDEX_RES_BIS_BIS].push(index_res + F::from_usize(2 * VECTOR_LEN));
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_24_COL_INPUT_START + i].push(*value);
        }

        // the rest of the trace is filled at the end of the execution (to get parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon24Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        num_cols_24()
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree_air(&self) -> usize {
        9
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 123
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: Poseidon24Cols<AB::F> = {
            let up = builder.up_f();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Poseidon24Cols<AB::F>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { std::ptr::read(&shorts[0]) }
        };

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                AB::F::from_usize(self.identifier().index()),
                cols.flag.clone(),
                &[cols.index_a.clone(), cols.index_b.clone(), cols.index_res.clone()],
            ));
        }

        builder.assert_bool(cols.flag.clone());
        builder.assert_eq(
            cols.index_a_bis.clone(),
            cols.index_a.clone() + AB::F::from_usize(VECTOR_LEN),
        );
        builder.assert_eq(
            cols.index_res_bis.clone(),
            cols.index_res.clone() + AB::F::from_usize(VECTOR_LEN),
        );
        builder.assert_eq(
            cols.index_res_bis_bis.clone(),
            cols.index_res.clone() + AB::F::from_usize(2 * VECTOR_LEN),
        );

        eval(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon24Cols<T> {
    pub flag: T,
    pub index_res: T,
    pub index_res_bis: T,
    pub index_res_bis_bis: T,
    pub index_a: T,
    pub index_a_bis: T,
    pub index_b: T,

    pub inputs: [T; WIDTH_24],
    pub beginning_full_rounds: [[T; WIDTH_24]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH_24]; HALF_FINAL_FULL_ROUNDS],
}

fn eval<AB: AirBuilder>(builder: &mut AB, local: &Poseidon24Cols<AB::F>) {
    let mut state: [_; WIDTH_24] = local.inputs.clone().map(|x| x);

    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut state);

    for round in 0..HALF_INITIAL_FULL_ROUNDS {
        eval_2_full_rounds(
            &mut state,
            &local.beginning_full_rounds[round],
            &KOALABEAR_RC24_EXTERNAL_INITIAL[2 * round],
            &KOALABEAR_RC24_EXTERNAL_INITIAL[2 * round + 1],
            builder,
        );
    }

    for (round, cst) in KOALABEAR_RC24_INTERNAL.iter().enumerate().take(PARTIAL_ROUNDS) {
        eval_partial_round(&mut state, &local.partial_rounds[round], *cst, builder);
    }

    for round in 0..HALF_FINAL_FULL_ROUNDS - 1 {
        eval_2_full_rounds(
            &mut state,
            &local.ending_full_rounds[round],
            &KOALABEAR_RC24_EXTERNAL_FINAL[2 * round],
            &KOALABEAR_RC24_EXTERNAL_FINAL[2 * round + 1],
            builder,
        );
    }

    eval_last_2_full_rounds(
        &mut state,
        &local.ending_full_rounds[HALF_FINAL_FULL_ROUNDS - 1],
        &KOALABEAR_RC24_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1)],
        &KOALABEAR_RC24_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1) + 1],
        builder,
    );
}

pub(super) const fn num_cols_24() -> usize {
    size_of::<Poseidon24Cols<u8>>()
}

#[inline]
fn eval_2_full_rounds<AB: AirBuilder>(
    state: &mut [AB::F; WIDTH_24],
    post_full_round: &[AB::F; WIDTH_24],
    round_constants_1: &[F; WIDTH_24],
    round_constants_2: &[F; WIDTH_24],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(state_i.clone(), post_i.clone());
        *state_i = post_i.clone();
    }
}

#[inline]
fn eval_last_2_full_rounds<AB: AirBuilder>(
    state: &mut [AB::F; WIDTH_24],
    post_full_round: &[AB::F; WIDTH_24],
    round_constants_1: &[F; WIDTH_24],
    round_constants_2: &[F; WIDTH_24],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(state_i.clone(), post_i.clone());
        // *state_i = post_i.clone() ;
    }
}

#[inline]
fn eval_partial_round<AB: AirBuilder>(
    state: &mut [AB::F; WIDTH_24],
    post_partial_round: &AB::F,
    round_constant: F,
    builder: &mut AB,
) {
    add_koala_bear(&mut state[0], round_constant);
    state[0] = state[0].cube();

    builder.assert_eq(state[0].clone(), post_partial_round.clone());
    state[0] = post_partial_round.clone();

    GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(state);
}

#[inline(always)]
fn add_koala_bear<A: 'static>(a: &mut A, value: F) {
    if TypeId::of::<A>() == TypeId::of::<F>() {
        *unsafe { std::mem::transmute::<&mut A, &mut F>(a) } += value;
    } else if TypeId::of::<A>() == TypeId::of::<EF>() {
        *unsafe { std::mem::transmute::<&mut A, &mut EF>(a) } += value;
    } else if TypeId::of::<A>() == TypeId::of::<FPacking<F>>() {
        *unsafe { std::mem::transmute::<&mut A, &mut FPacking<F>>(a) } += value;
    } else if TypeId::of::<A>() == TypeId::of::<EFPacking<EF>>() {
        *unsafe { std::mem::transmute::<&mut A, &mut EFPacking<EF>>(a) } += FPacking::<F>::from(value);
    } else {
        unreachable!()
    }
}
