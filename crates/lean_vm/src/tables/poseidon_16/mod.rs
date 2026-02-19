use std::any::TypeId;

use crate::{tables::poseidon_16::trace_gen::default_poseidon_row, *};
use backend::*;
use utils::{ToUsize, poseidon16_compress};

mod trace_gen;
pub use trace_gen::fill_trace_poseidon_16;

pub(super) const WIDTH: usize = 16;
const HALF_INITIAL_FULL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_INITIAL.len() / 2;
const PARTIAL_ROUNDS: usize = KOALABEAR_RC16_INTERNAL.len();
const HALF_FINAL_FULL_ROUNDS: usize = KOALABEAR_RC16_EXTERNAL_FINAL.len() / 2;

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_A: ColIndex = 1;
pub const POSEIDON_16_COL_B: ColIndex = 2;
pub const POSEIDON_16_COL_RES: ColIndex = 3;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 4;
const POSEIDON_16_COL_OUTPUT_START: ColIndex = num_cols_poseidon_16() - 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon16Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon16"
    }

    fn table(&self) -> Table {
        Table::poseidon16()
    }

    fn lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_16_COL_A,
                values: (POSEIDON_16_COL_INPUT_START..POSEIDON_16_COL_INPUT_START + DIGEST_LEN).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_16_COL_B,
                values: (POSEIDON_16_COL_INPUT_START + DIGEST_LEN..POSEIDON_16_COL_INPUT_START + DIGEST_LEN * 2)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_16_COL_RES,
                values: (POSEIDON_16_COL_OUTPUT_START..POSEIDON_16_COL_OUTPUT_START + DIGEST_LEN).collect(),
            },
        ]
    }

    fn lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn bus(&self) -> Bus {
        Bus {
            table: BusTable::Constant(self.table()),
            direction: BusDirection::Pull,
            selector: POSEIDON_16_COL_FLAG,
            data: vec![POSEIDON_16_COL_A, POSEIDON_16_COL_B, POSEIDON_16_COL_RES],
        }
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
        _: usize,
        _: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), DIGEST_LEN)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST_LEN)?;

        let mut input = [F::ZERO; DIGEST_LEN * 2];
        input[..DIGEST_LEN].copy_from_slice(&arg0);
        input[DIGEST_LEN..].copy_from_slice(&arg1);

        let output = match ctx.poseidon16_precomputed.get(*ctx.n_poseidon16_precomputed_used) {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon16_precomputed_used += 1;
                precomputed.1
            }
            _ => poseidon16_compress(input),
        };

        let res_a: [F; DIGEST_LEN] = output[..DIGEST_LEN].try_into().unwrap();

        ctx.memory.set_slice(index_res_a.to_usize(), &res_a)?;

        trace.base[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_16_COL_A].push(arg_a);
        trace.base[POSEIDON_16_COL_B].push(arg_b);
        trace.base[POSEIDON_16_COL_RES].push(index_res_a);
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
        num_cols_poseidon_16()
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
        BUS as usize + 76
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
                AB::F::from_usize(self.table().index()),
                cols.flag.clone(),
                &[cols.index_a.clone(), cols.index_b.clone(), cols.index_res.clone()],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[cols.index_a.clone(), cols.index_b.clone(), cols.index_res.clone()]);
        }

        builder.assert_bool(cols.flag.clone());

        eval(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon2Cols<T> {
    pub flag: T,
    pub index_a: T,
    pub index_b: T,
    pub index_res: T,

    pub inputs: [T; WIDTH],
    pub beginning_full_rounds: [[T; WIDTH]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH]; HALF_FINAL_FULL_ROUNDS - 1],
    pub outputs: [T; WIDTH / 2],
}

fn eval<AB: AirBuilder>(builder: &mut AB, local: &Poseidon2Cols<AB::F>) {
    let mut state: [_; WIDTH] = local.inputs.clone();

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

    for (round, cst) in KOALABEAR_RC16_INTERNAL.iter().enumerate().take(PARTIAL_ROUNDS) {
        eval_partial_round(&mut state, &local.partial_rounds[round], *cst, builder);
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
        &local.inputs,
        &mut state,
        &local.outputs,
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1)],
        &KOALABEAR_RC16_EXTERNAL_FINAL[2 * (HALF_FINAL_FULL_ROUNDS - 1) + 1],
        builder,
    );
}

pub const fn num_cols_poseidon_16() -> usize {
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
    initial_state: &[AB::F; WIDTH],
    state: &mut [AB::F; WIDTH],
    outputs: &[AB::F; WIDTH / 2],
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
    // add inputs to outputs (for compression)
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += init_state_i.clone();
    }
    for (state_i, output_i) in state.iter_mut().zip(outputs) {
        builder.assert_eq(state_i.clone(), output_i.clone());
        *state_i = output_i.clone();
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
    } else if TypeId::of::<A>() == TypeId::of::<SymbolicExpression<KoalaBear>>() {
        *unsafe { std::mem::transmute::<&mut A, &mut SymbolicExpression<KoalaBear>>(a) } += value;
    } else {
        dbg!(std::any::type_name::<A>());
        unreachable!()
    }
}
