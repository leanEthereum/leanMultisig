use std::any::TypeId;

use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;
use utils::{ToUsize, poseidon16_compress};

/// Dispatch `mds_circ_16` through concrete types.
/// For `SymbolicExpression` we use the dense form so the zkDSL generator can
/// emit `dot_product_be` precompile calls instead of Karatsuba arithmetic.
#[inline(always)]
fn mds_air_16<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH_16]) {
    if TypeId::of::<A>() == TypeId::of::<SymbolicExpression<KoalaBear>>() {
        dense_mat_vec_air_16(mds_dense_16(), state);
        return;
    }
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                mds_circ_16::<$t>(unsafe { &mut *(state as *mut [A; WIDTH_16] as *mut [$t; WIDTH_16]) });
                return;
            }
        };
    }
    dispatch!(F);
    dispatch!(EF);
    dispatch!(FPacking<F>);
    dispatch!(EFPacking<EF>);
    unreachable!()
}

fn mds_dense_16() -> &'static [[F; 16]; 16] {
    use std::sync::OnceLock;
    static MAT: OnceLock<[[KoalaBear; 16]; 16]> = OnceLock::new();
    MAT.get_or_init(|| {
        let cols: [[F; 16]; 16] = std::array::from_fn(|j| {
            let mut e = [F::ZERO; 16];
            e[j] = F::ONE;
            mds_circ_16(&mut e);
            e
        });
        std::array::from_fn(|i| std::array::from_fn(|j| cols[j][i]))
    })
}

/// Add a `KoalaBear` constant to any AIR type.
#[inline(always)]
fn add_kb<A: 'static>(a: &mut A, value: F) {
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

/// Multiply any AIR type by a `KoalaBear` constant.
#[inline(always)]
fn mul_kb<A: PrimeCharacteristicRing + 'static>(a: A, value: F) -> A {
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
pub use trace_gen::{default_poseidon_16_row, fill_trace_poseidon_16};

pub(super) const WIDTH_16: usize = 16;
const HALF_INITIAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;
const PARTIAL_ROUNDS: usize = POSEIDON1_PARTIAL_ROUNDS;
const HALF_FINAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;

pub const POSEIDON_PRECOMPILE_DATA: usize = 1; // domain separation: Poseidon16=1, Poseidon24=2 or 3 or 4, ExtensionOp>=8

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = 2;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = 3;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_16_COL_OUTPUT_START: ColIndex = num_cols_poseidon_16() - 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon16Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon16_compress"
    }

    fn table(&self) -> Table {
        Table::poseidon16()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_INPUT_LEFT,
                values: (POSEIDON_16_COL_INPUT_START..POSEIDON_16_COL_INPUT_START + DIGEST_LEN).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_INPUT_RIGHT,
                values: (POSEIDON_16_COL_INPUT_START + DIGEST_LEN..POSEIDON_16_COL_INPUT_START + DIGEST_LEN * 2)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_INPUT_RES,
                values: (POSEIDON_16_COL_OUTPUT_START..POSEIDON_16_COL_OUTPUT_START + DIGEST_LEN).collect(),
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_16_COL_FLAG,
            data: vec![
                BusData::Constant(POSEIDON_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_16_COL_INDEX_INPUT_LEFT),
                BusData::Column(POSEIDON_16_COL_INDEX_INPUT_RIGHT),
                BusData::Column(POSEIDON_16_COL_INDEX_INPUT_RES),
            ],
        }
    }

    fn padding_row(&self) -> Vec<F> {
        // depends on null_poseidon_16_hash_ptr (cf lean_prover/trace_gen.rs)
        unreachable!()
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        _: usize,
        _: usize,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), DIGEST_LEN)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST_LEN)?;

        let mut input = [F::ZERO; DIGEST_LEN * 2];
        input[..DIGEST_LEN].copy_from_slice(&arg0);
        input[DIGEST_LEN..].copy_from_slice(&arg1);

        let output = poseidon16_compress(input);

        let res_a: [F; DIGEST_LEN] = output[..DIGEST_LEN].try_into().unwrap();

        ctx.memory.set_slice(index_res_a.to_usize(), &res_a)?;

        trace.columns[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_LEFT].push(arg_a);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RES].push(index_res_a);
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_16_COL_INPUT_START + i].push(*value);
        }

        // the rest of the trace is filled at the end of the execution (to get parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon16Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_16()
    }
    fn degree_air(&self) -> usize {
        9
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 76
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cols: Poseidon1Cols16<AB::IF> = {
            let up = builder.up();
            let (prefix, shorts, suffix) = unsafe { up.align_to::<Poseidon1Cols16<AB::IF>>() };
            debug_assert!(prefix.is_empty(), "Alignment should match");
            debug_assert!(suffix.is_empty(), "Alignment should match");
            debug_assert_eq!(shorts.len(), 1);
            unsafe { std::ptr::read(&shorts[0]) }
        };

        // Bus data: [POSEIDON_PRECOMPILE_DATA (constant), a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[
                    AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                    cols.index_a,
                    cols.index_b,
                    cols.index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[
                AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                cols.index_a,
                cols.index_b,
                cols.index_res,
            ]);
        }

        builder.assert_bool(cols.flag);

        eval_poseidon1_16(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon1Cols16<T> {
    pub flag: T,
    pub index_a: T,
    pub index_b: T,
    pub index_res: T,

    pub inputs: [T; WIDTH_16],
    pub beginning_full_rounds: [[T; WIDTH_16]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH_16]; HALF_FINAL_FULL_ROUNDS - 1],
    pub outputs: [T; WIDTH_16 / 2],
}

fn eval_poseidon1_16<AB: AirBuilder>(builder: &mut AB, local: &Poseidon1Cols16<AB::IF>) {
    let mut state: [_; WIDTH_16] = local.inputs;

    let initial_constants = poseidon1_initial_constants();
    for round in 0..HALF_INITIAL_FULL_ROUNDS {
        eval_2_full_rounds_16(
            &mut state,
            &local.beginning_full_rounds[round],
            &initial_constants[2 * round],
            &initial_constants[2 * round + 1],
            builder,
        );
    }

    // --- Sparse partial rounds ---
    // Transition: add first-round constants, multiply by m_i
    let frc = poseidon1_sparse_first_round_constants();
    for (s, &c) in state.iter_mut().zip(frc.iter()) {
        add_kb(s, c);
    }
    dense_mat_vec_air_16(poseidon1_sparse_m_i(), &mut state);

    let first_rows = poseidon1_sparse_first_row();
    let v_vecs = poseidon1_sparse_v();
    let scalar_rc = poseidon1_sparse_scalar_round_constants();
    for round in 0..PARTIAL_ROUNDS {
        // S-box on state[0]
        state[0] = state[0].cube();
        builder.assert_eq(state[0], local.partial_rounds[round]);
        state[0] = local.partial_rounds[round];
        // Scalar round constant (not on last round)
        if round < PARTIAL_ROUNDS - 1 {
            add_kb(&mut state[0], scalar_rc[round]);
        }
        // Sparse matrix: new_s0 = dot(first_row, state), state[i] += old_s0 * v[i-1]
        sparse_mat_air_16(&mut state, &first_rows[round], &v_vecs[round]);
    }

    let final_constants = poseidon1_final_constants();
    for round in 0..HALF_FINAL_FULL_ROUNDS - 1 {
        eval_2_full_rounds_16(
            &mut state,
            &local.ending_full_rounds[round],
            &final_constants[2 * round],
            &final_constants[2 * round + 1],
            builder,
        );
    }

    eval_last_2_full_rounds_16(
        &local.inputs,
        &mut state,
        &local.outputs,
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS - 1)],
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS - 1) + 1],
        builder,
    );
}

pub const fn num_cols_poseidon_16() -> usize {
    size_of::<Poseidon1Cols16<u8>>()
}

#[inline]
fn eval_2_full_rounds_16<AB: AirBuilder>(
    state: &mut [AB::IF; WIDTH_16],
    post_full_round: &[AB::IF; WIDTH_16],
    round_constants_1: &[F; WIDTH_16],
    round_constants_2: &[F; WIDTH_16],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_kb(s, *r);
        *s = s.cube();
    }
    mds_air_16(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_kb(s, *r);
        *s = s.cube();
    }
    mds_air_16(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(*state_i, *post_i);
        *state_i = *post_i;
    }
}

#[inline]
fn eval_last_2_full_rounds_16<AB: AirBuilder>(
    initial_state: &[AB::IF; WIDTH_16],
    state: &mut [AB::IF; WIDTH_16],
    outputs: &[AB::IF; WIDTH_16 / 2],
    round_constants_1: &[F; WIDTH_16],
    round_constants_2: &[F; WIDTH_16],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_kb(s, *r);
        *s = s.cube();
    }
    mds_air_16(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_kb(s, *r);
        *s = s.cube();
    }
    mds_air_16(state);
    // add inputs to outputs (for compression)
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += *init_state_i;
    }
    for (state_i, output_i) in state.iter_mut().zip(outputs) {
        builder.assert_eq(*state_i, *output_i);
        *state_i = *output_i;
    }
}

#[inline]
fn dense_mat_vec_air_16<A: PrimeCharacteristicRing + 'static>(mat: &[[F; 16]; 16], state: &mut [A; WIDTH_16]) {
    let input = *state;
    for i in 0..WIDTH_16 {
        let mut acc = A::ZERO;
        for j in 0..WIDTH_16 {
            acc += mul_kb(input[j], mat[i][j]);
        }
        state[i] = acc;
    }
}

#[inline]
fn sparse_mat_air_16<A: PrimeCharacteristicRing + 'static>(
    state: &mut [A; WIDTH_16],
    first_row: &[F; WIDTH_16],
    v: &[F; WIDTH_16],
) {
    let old_s0 = state[0];
    let mut new_s0 = A::ZERO;
    for j in 0..WIDTH_16 {
        new_s0 += mul_kb(state[j], first_row[j]);
    }
    state[0] = new_s0;
    for i in 1..WIDTH_16 {
        state[i] += mul_kb(old_s0, v[i - 1]);
    }
}
