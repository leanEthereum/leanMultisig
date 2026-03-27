use std::any::TypeId;

use crate::*;
use backend::*;
use utils::{ToUsize, poseidon24_compress_0_9, poseidon24_permute_0_9, poseidon24_permute_9_18};

/// Dispatch `mds_circ_24` through concrete types.
#[inline(always)]
fn mds_air_24<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH_24]) {
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                mds_circ_24::<$t>(unsafe { &mut *(state as *mut [A; WIDTH_24] as *mut [$t; WIDTH_24]) });
                return;
            }
        };
    }
    dispatch!(F);
    dispatch!(EF);
    dispatch!(FPacking<F>);
    dispatch!(EFPacking<EF>);
    dispatch!(SymbolicExpression<KoalaBear>);
    unreachable!()
}

#[inline(always)]
fn add_kb_24<A: 'static>(a: &mut A, value: F) {
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                *unsafe { &mut *(a as *mut A as *mut $t) } += value;
                return;
            }
        };
    }
    dispatch!(F);
    dispatch!(EF);
    dispatch!(FPacking<F>);
    dispatch!(EFPacking<EF>);
    dispatch!(SymbolicExpression<KoalaBear>);
    unreachable!()
}

#[inline(always)]
fn mul_kb_24<A: PrimeCharacteristicRing + 'static>(a: A, value: F) -> A {
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                let r = unsafe { std::ptr::read(&a as *const A as *const $t) } * value;
                return unsafe { std::ptr::read(&r as *const $t as *const A) };
            }
        };
    }
    dispatch!(F);
    dispatch!(EF);
    dispatch!(FPacking<F>);
    dispatch!(EFPacking<EF>);
    dispatch!(SymbolicExpression<KoalaBear>);
    unreachable!()
}

mod trace_gen;
pub use trace_gen::default_poseidon_24_row;
pub use trace_gen::fill_trace_poseidon_24;

pub(super) const WIDTH_24: usize = 24;
const HALF_INITIAL_FULL_ROUNDS_24: usize = POSEIDON1_HALF_FULL_ROUNDS_24 / 2;
const PARTIAL_ROUNDS_24: usize = POSEIDON1_PARTIAL_ROUNDS_24;
const HALF_FINAL_FULL_ROUNDS_24: usize = POSEIDON1_HALF_FULL_ROUNDS_24 / 2;

pub const POSEIDON_24_PRECOMPILE_DATA_OFFSET: usize = 2; // domain separation: Poseidon16=1, Poseidon24= 2 or 3 or 4, ExtensionOp>=8

// 3 modes for Poseidon24 precompile:
//   compress_0_9 (mode=0): feedforward + output[0..9]    -> precompile_data = 2
//   permute_0_9  (mode=1): permutation + output[0..9] -> precompile_data = 3
//   permute_9_18 (mode=2): permutation + output[9..18]-> precompile_data = 4
// 2 committed boolean columns: is_compress_0_9, is_permute_0_9
// 3rd mode deduced: is_permute_9_18 = 1 - is_compress_0_9 - is_permute_0_9
pub const POSEIDON_24_MODE_COMPRESS_0_9: usize = 0;
pub const POSEIDON_24_MODE_PERMUTE_0_9: usize = 1;
pub const POSEIDON_24_MODE_PERMUTE_9_18: usize = 2;

pub const POSEIDON_24_INPUT_LEFT_SIZE: usize = 9;
pub const POSEIDON_24_INPUT_RIGHT_SIZE: usize = 15;
pub const POSEIDON_24_OUTPUT_SIZE: usize = 9;

pub const POSEIDON_24_COL_FLAG: ColIndex = 0;
pub const POSEIDON_24_COL_IS_COMPRESS_0_9: ColIndex = 1;
pub const POSEIDON_24_COL_IS_PERMUTE_0_9: ColIndex = 2;
pub const POSEIDON_24_COL_INDEX_INPUT_LEFT: ColIndex = 3;
pub const POSEIDON_24_COL_INDEX_INPUT_RIGHT: ColIndex = 4;
pub const POSEIDON_24_COL_INDEX_RES: ColIndex = 5;
pub const POSEIDON_24_COL_INPUT_START: ColIndex = 6;
pub const POSEIDON_24_COL_OUTPUT_START: ColIndex = num_cols_poseidon_24() - POSEIDON_24_OUTPUT_SIZE;

// virtual columns (not committed)
pub const POSEIDON_24_COL_PRECOMPILE_DATA: usize = num_cols_poseidon_24();

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon24Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon24Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon24_compress"
    }

    fn table(&self) -> Table {
        Table::poseidon24()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_INPUT_LEFT,
                values: (POSEIDON_24_COL_INPUT_START..POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_INPUT_RIGHT,
                values: (POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE
                    ..POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE + POSEIDON_24_INPUT_RIGHT_SIZE)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_RES,
                values: (POSEIDON_24_COL_OUTPUT_START..POSEIDON_24_COL_OUTPUT_START + POSEIDON_24_OUTPUT_SIZE)
                    .collect(),
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_24_COL_FLAG,
            data: vec![
                BusData::Column(POSEIDON_24_COL_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_24_COL_INDEX_INPUT_LEFT),
                BusData::Column(POSEIDON_24_COL_INDEX_INPUT_RIGHT),
                BusData::Column(POSEIDON_24_COL_INDEX_RES),
            ],
        }
    }

    fn n_columns_total(&self) -> usize {
        self.n_columns() + 1 // +1 for POSEIDON_24_POSEIDON_24_COL_PRECOMPILE_DATA
    }

    fn padding_row(&self) -> Vec<F> {
        // depends on null_poseidon_24_hash_ptr (cf lean_prover/trace_gen.rs)
        unreachable!()
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        index_input_left: F,
        index_input_right: F,
        index_res: F,
        mode: usize,
        _: usize,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        assert!(mode <= POSEIDON_24_MODE_PERMUTE_9_18, "invalid poseidon24 mode={mode}");
        let is_compress_0_9 = mode == POSEIDON_24_MODE_COMPRESS_0_9;
        let is_permute_0_9 = mode == POSEIDON_24_MODE_PERMUTE_0_9;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg0 = ctx
            .memory
            .get_slice(index_input_left.to_usize(), POSEIDON_24_INPUT_LEFT_SIZE)?;
        let arg1 = ctx
            .memory
            .get_slice(index_input_right.to_usize(), POSEIDON_24_INPUT_RIGHT_SIZE)?;

        let mut input = [F::ZERO; POSEIDON_24_INPUT_LEFT_SIZE + POSEIDON_24_INPUT_RIGHT_SIZE];
        input[..POSEIDON_24_INPUT_LEFT_SIZE].copy_from_slice(&arg0);
        input[POSEIDON_24_INPUT_LEFT_SIZE..].copy_from_slice(&arg1);

        let result = match mode {
            POSEIDON_24_MODE_COMPRESS_0_9 => poseidon24_compress_0_9(input),
            POSEIDON_24_MODE_PERMUTE_0_9 => poseidon24_permute_0_9(input),
            POSEIDON_24_MODE_PERMUTE_9_18 => poseidon24_permute_9_18(input),
            _ => unreachable!(),
        };

        let res_a: [F; POSEIDON_24_OUTPUT_SIZE] = result[..POSEIDON_24_OUTPUT_SIZE].try_into().unwrap();

        ctx.memory.set_slice(index_res.to_usize(), &res_a)?;

        trace.columns[POSEIDON_24_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_24_COL_IS_COMPRESS_0_9].push(F::from_bool(is_compress_0_9));
        trace.columns[POSEIDON_24_COL_IS_PERMUTE_0_9].push(F::from_bool(is_permute_0_9));
        trace.columns[POSEIDON_24_COL_INDEX_INPUT_LEFT].push(index_input_left);
        trace.columns[POSEIDON_24_COL_INDEX_INPUT_RIGHT].push(index_input_right);
        trace.columns[POSEIDON_24_COL_INDEX_RES].push(index_res);
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_24_COL_INPUT_START + i].push(*value);
        }
        trace.columns[POSEIDON_24_COL_PRECOMPILE_DATA].push(F::from_usize(POSEIDON_24_PRECOMPILE_DATA_OFFSET + mode));

        // the rest of the trace is filled at the end of the execution (for parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon24Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_24()
    }
    fn degree_air(&self) -> usize {
        10
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 107
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: Poseidon1Cols24<AB::IF> = {
            let up = builder.up();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Poseidon1Cols24<AB::IF>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { std::ptr::read(&shorts[0]) }
        };

        let precompile_data = AB::IF::from_usize(POSEIDON_24_PRECOMPILE_DATA_OFFSET)
            + cols.is_compress_0_9 * AB::IF::from_usize(POSEIDON_24_MODE_COMPRESS_0_9)
            + cols.is_permute_0_9 * AB::IF::from_usize(POSEIDON_24_MODE_PERMUTE_0_9)
            + (AB::IF::ONE - cols.is_compress_0_9 - cols.is_permute_0_9) // is_permute_9_18
                * AB::IF::from_usize(POSEIDON_24_MODE_PERMUTE_9_18);

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[
                    precompile_data,
                    cols.index_input_left,
                    cols.index_input_right,
                    cols.index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[
                precompile_data,
                cols.index_input_left,
                cols.index_input_right,
                cols.index_res,
            ]);
        }

        builder.assert_bool(cols.flag);
        builder.assert_bool(cols.is_compress_0_9);
        builder.assert_bool(cols.is_permute_0_9);

        let is_compress = cols.is_compress_0_9;
        let is_output_0_9 = cols.is_compress_0_9 + cols.is_permute_0_9;

        eval_poseidon1_24(builder, &cols, is_compress, is_output_0_9)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon1Cols24<T> {
    pub flag: T,
    pub is_compress_0_9: T,
    pub is_permute_0_9: T,
    pub index_input_left: T,
    pub index_input_right: T,
    pub index_res: T,

    pub inputs: [T; WIDTH_24],
    pub beginning_full_rounds: [[T; WIDTH_24]; HALF_INITIAL_FULL_ROUNDS_24],
    pub partial_rounds: [T; PARTIAL_ROUNDS_24],
    pub ending_full_rounds: [[T; WIDTH_24]; HALF_FINAL_FULL_ROUNDS_24 - 1],
    pub outputs: [T; POSEIDON_24_OUTPUT_SIZE],
}

fn eval_poseidon1_24<AB: AirBuilder>(
    builder: &mut AB,
    local: &Poseidon1Cols24<AB::IF>,
    is_compress: AB::IF,
    is_output_0_9: AB::IF,
) {
    let mut state: [_; WIDTH_24] = local.inputs;

    // No initial linear layer for Poseidon1

    let initial_constants = poseidon1_24_initial_constants();
    for round in 0..HALF_INITIAL_FULL_ROUNDS_24 {
        eval_2_full_rounds_24(
            &mut state,
            &local.beginning_full_rounds[round],
            &initial_constants[2 * round],
            &initial_constants[2 * round + 1],
            builder,
        );
    }

    // --- Sparse partial rounds ---
    let frc = poseidon1_24_sparse_first_round_constants();
    for (s, &c) in state.iter_mut().zip(frc.iter()) {
        add_kb_24(s, c);
    }
    dense_mat_vec_air_24(poseidon1_24_sparse_m_i(), &mut state);

    let first_rows = poseidon1_24_sparse_first_row();
    let v_vecs = poseidon1_24_sparse_v();
    let scalar_rc = poseidon1_24_sparse_scalar_round_constants();
    for round in 0..PARTIAL_ROUNDS_24 {
        // S-box on state[0]
        state[0] = state[0].cube();
        builder.assert_eq(state[0], local.partial_rounds[round]);
        state[0] = local.partial_rounds[round];
        // Scalar round constant (not on last round)
        if round < PARTIAL_ROUNDS_24 - 1 {
            add_kb_24(&mut state[0], scalar_rc[round]);
        }
        // Sparse matrix
        sparse_mat_air_24(&mut state, &first_rows[round], &v_vecs[round]);
    }

    let final_constants = poseidon1_24_final_constants();
    for round in 0..HALF_FINAL_FULL_ROUNDS_24 - 1 {
        eval_2_full_rounds_24(
            &mut state,
            &local.ending_full_rounds[round],
            &final_constants[2 * round],
            &final_constants[2 * round + 1],
            builder,
        );
    }

    eval_last_2_full_rounds_24(
        &local.inputs,
        &mut state,
        &local.outputs,
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS_24 - 1)],
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS_24 - 1) + 1],
        is_compress,
        is_output_0_9,
        builder,
    );
}

pub const fn num_cols_poseidon_24() -> usize {
    size_of::<Poseidon1Cols24<u8>>()
}

#[inline]
fn eval_2_full_rounds_24<AB: AirBuilder>(
    state: &mut [AB::IF; WIDTH_24],
    post_full_round: &[AB::IF; WIDTH_24],
    round_constants_1: &[F; WIDTH_24],
    round_constants_2: &[F; WIDTH_24],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_kb_24(s, *r);
        *s = s.cube();
    }
    mds_air_24(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_kb_24(s, *r);
        *s = s.cube();
    }
    mds_air_24(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(*state_i, *post_i);
        *state_i = *post_i;
    }
}

#[inline]
#[allow(clippy::too_many_arguments)]
fn eval_last_2_full_rounds_24<AB: AirBuilder>(
    initial_state: &[AB::IF; WIDTH_24],
    state: &mut [AB::IF; WIDTH_24],
    outputs: &[AB::IF; POSEIDON_24_OUTPUT_SIZE],
    round_constants_1: &[F; WIDTH_24],
    round_constants_2: &[F; WIDTH_24],
    is_compress: AB::IF,
    is_output_0_9: AB::IF,
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_kb_24(s, *r);
        *s = s.cube();
    }
    mds_air_24(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_kb_24(s, *r);
        *s = s.cube();
    }
    mds_air_24(state);
    // conditional feedforward: only for compress mode
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += *init_state_i * is_compress;
    }
    for ((output_i, state_i), state_9_plus_i) in outputs
        .iter()
        .zip(&state[..POSEIDON_24_OUTPUT_SIZE])
        .zip(&state[POSEIDON_24_OUTPUT_SIZE..][..POSEIDON_24_OUTPUT_SIZE])
    {
        builder.assert_eq(
            *output_i,
            *state_i * is_output_0_9 + *state_9_plus_i * (AB::IF::ONE - is_output_0_9),
        );
    }
}

#[inline]
fn dense_mat_vec_air_24<A: PrimeCharacteristicRing + 'static>(mat: &[[F; 24]; 24], state: &mut [A; WIDTH_24]) {
    let input = *state;
    for i in 0..WIDTH_24 {
        let mut acc = A::ZERO;
        for j in 0..WIDTH_24 {
            acc += mul_kb_24(input[j], mat[i][j]);
        }
        state[i] = acc;
    }
}

#[inline]
fn sparse_mat_air_24<A: PrimeCharacteristicRing + 'static>(
    state: &mut [A; WIDTH_24],
    first_row: &[F; WIDTH_24],
    v: &[F; WIDTH_24],
) {
    let old_s0 = state[0];
    let mut new_s0 = A::ZERO;
    for j in 0..WIDTH_24 {
        new_s0 += mul_kb_24(state[j], first_row[j]);
    }
    state[0] = new_s0;
    for i in 1..WIDTH_24 {
        state[i] += mul_kb_24(old_s0, v[i - 1]);
    }
}
