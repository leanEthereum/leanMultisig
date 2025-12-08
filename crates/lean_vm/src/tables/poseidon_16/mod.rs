use p3_poseidon2::GenericPoseidon2LinearLayers;
use std::{any::TypeId, array};

use crate::{tables::poseidon_16::trace_gen::default_poseidon_row, *};
use multilinear_toolkit::prelude::*;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_RC16_EXTERNAL_FINAL, KOALABEAR_RC16_EXTERNAL_INITIAL,
    KOALABEAR_RC16_INTERNAL,
};
use utils::{ToUsize, poseidon16_permute};

mod test;
mod trace_gen;

pub use trace_gen::generate_trace_poseidon_16;
pub use test::benchmark_prove_poseidon_16;

pub const POSEIDON_16_DEFAULT_COMPRESSION: bool = true;

pub(super) const WIDTH: usize = 16;
const HALF_INITIAL_FULL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_INITIAL.len() / 2;
const PARTIAL_ROUNDS: usize = KOALABEAR_RC16_INTERNAL.len();
const HALF_FINAL_FULL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_FINAL.len() / 2;

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_RES: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_RES_BIS: ColIndex = 2; // = if compressed { 0 } else { POSEIDON_16_COL_INDEX_RES + 1 }
pub const POSEIDON_16_COL_COMPRESSION: ColIndex = 3;
pub const POSEIDON_16_COL_INDEX_A: ColIndex = 4;
pub const POSEIDON_16_COL_INDEX_B: ColIndex = 5;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 6;
const POSEIDON_16_COL_OUTPUT_START: ColIndex = num_cols() - 16;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon16Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon16"
    }

    fn identifier(&self) -> Table {
        Table::poseidon16()
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
                index: POSEIDON_16_COL_INDEX_A,
                values: array::from_fn(|i| POSEIDON_16_COL_INPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_B,
                values: array::from_fn(|i| POSEIDON_16_COL_INPUT_START + VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_RES,
                values: array::from_fn(|i| POSEIDON_16_COL_OUTPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_RES_BIS,
                values: array::from_fn(|i| POSEIDON_16_COL_OUTPUT_START + VECTOR_LEN + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        assert!(BUS);
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: BusSelector::Column(POSEIDON_16_COL_FLAG),
            data: vec![
                POSEIDON_16_COL_INDEX_A,
                POSEIDON_16_COL_INDEX_B,
                POSEIDON_16_COL_INDEX_RES,
                POSEIDON_16_COL_COMPRESSION,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        default_poseidon_row()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        is_compression: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(is_compression == 0 || is_compression == 1);
        let is_compression = is_compression == 1;
        let trace = ctx.traces.get_mut(&self.identifier()).unwrap();

        let arg0 = ctx.memory.get_vector(arg_a.to_usize())?;
        let arg1 = ctx.memory.get_vector(arg_b.to_usize())?;

        let mut input = [F::ZERO; VECTOR_LEN * 2];
        input[..VECTOR_LEN].copy_from_slice(&arg0);
        input[VECTOR_LEN..].copy_from_slice(&arg1);

        let output = match ctx.poseidon16_precomputed.get(*ctx.n_poseidon16_precomputed_used) {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon16_precomputed_used += 1;
                precomputed.1
            }
            _ => poseidon16_permute(input),
        };

        let res_a: [F; VECTOR_LEN] = output[..VECTOR_LEN].try_into().unwrap();
        let (index_res_b, res_b): (F, [F; VECTOR_LEN]) = if is_compression {
            (F::from_usize(ZERO_VEC_PTR), [F::ZERO; VECTOR_LEN])
        } else {
            (index_res_a + F::ONE, output[VECTOR_LEN..].try_into().unwrap())
        };

        ctx.memory.set_vector(index_res_a.to_usize(), res_a)?;
        ctx.memory.set_vector(index_res_b.to_usize(), res_b)?;

        trace.base[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_16_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_16_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_16_COL_INDEX_RES].push(index_res_a);
        trace.base[POSEIDON_16_COL_INDEX_RES_BIS].push(index_res_b);
        trace.base[POSEIDON_16_COL_COMPRESSION].push(F::from_bool(is_compression));
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_16_COL_INPUT_START + i].push(*value);
        }
        
        // the rest of the trace is filled at the end of the execution (to get parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon16Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        num_cols()
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree_air(&self) -> usize {
        10
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 87
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: Poseidon2Cols<AB::F> = {
            let up = builder.up_f();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Poseidon2Cols<AB::F>>() };
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
                &[
                    cols.index_a.clone(),
                    cols.index_b.clone(),
                    cols.index_res.clone(),
                    cols.compress.clone(),
                ],
            ));
        }

        builder.assert_bool(cols.flag.clone());
        builder.assert_bool(cols.compress.clone());
        builder.assert_eq(
            cols.index_res_bis.clone(),
            (cols.index_res.clone() + AB::F::ONE) * (AB::F::ONE - cols.compress.clone()),
        );

        eval(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon2Cols<T> {
    pub flag: T,
    pub index_res: T,
    pub index_res_bis: T,
    pub compress: T,
    pub index_a: T,
    pub index_b: T,

    pub inputs: [T; WIDTH],
    pub beginning_full_rounds: [[T; WIDTH]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH]; HALF_FINAL_FULL_ROUNDS],
}

fn eval<AB: AirBuilder>(builder: &mut AB, local: &Poseidon2Cols<AB::F>) {
    let mut state: [_; WIDTH] = local.inputs.clone().map(|x| x);

    GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(&mut state);

    for round in 0..HALF_INITIAL_FULL_ROUNDS {
        eval_2_full_rounds(
            &mut state,
            &local.beginning_full_rounds[round],
            &KOALABEAR_RC16_EXTERNAL_INITIAL[2 * round],
            &KOALABEAR_RC16_EXTERNAL_INITIAL[2 * round + 1],
            builder,
        );
    }

    for round in 0..PARTIAL_ROUNDS {
        eval_partial_round(
            &mut state,
            &local.partial_rounds[round],
            KOALABEAR_RC16_INTERNAL[round],
            builder,
        );
    }

    for round in 0..HALF_FINAL_FULL_ROUNDS - 1 {
        eval_2_full_rounds(
            &mut state,
            &local.ending_full_rounds[round],
            &KOALABEAR_RC16_EXTERNAL_FINAL[2 * round],
            &KOALABEAR_RC16_EXTERNAL_FINAL[2 * round + 1],
            builder,
        );
    }

    eval_last_2_full_rounds(
        &mut state,
        &local.ending_full_rounds[HALF_FINAL_FULL_ROUNDS - 1],
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1)],
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1) + 1],
        local.compress.clone(),
        builder,
    );
}

pub(super) const fn num_cols() -> usize {
    size_of::<Poseidon2Cols<u8>>()
}

#[inline]
fn eval_2_full_rounds<AB: AirBuilder>(
    state: &mut [AB::F; WIDTH],
    post_full_round: &[AB::F; WIDTH],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
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
    state: &mut [AB::F; WIDTH],
    post_full_round: &[AB::F; WIDTH],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
    compress: AB::F,
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
    for (state_i, post_i) in state.iter_mut().zip(post_full_round).take(WIDTH / 2) {
        builder.assert_eq(state_i.clone(), post_i.clone());
        *state_i = post_i.clone().into();
    }
    for (state_i, post_i) in state.iter_mut().zip(post_full_round).skip(WIDTH / 2) {
        builder.assert_eq(state_i.clone() * -(compress.clone() - AB::F::ONE), post_i.clone());
        *state_i = post_i.clone().into();
    }
}

#[inline]
fn eval_partial_round<AB: AirBuilder>(
    state: &mut [AB::F; WIDTH],
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
