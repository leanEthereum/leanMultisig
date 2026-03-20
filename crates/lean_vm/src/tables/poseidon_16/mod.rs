use std::any::TypeId;

use crate::*;
use backend::*;
use utils::{ToUsize, poseidon16_compress};

mod trace_gen;
pub use trace_gen::{default_poseidon_16_row, fill_trace_poseidon_16};

pub(super) const WIDTH: usize = 16;
const HALF_INITIAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;
const PARTIAL_ROUNDS: usize = POSEIDON1_PARTIAL_ROUNDS;
const HALF_FINAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;

pub const POSEIDON_PRECOMPILE_DATA: usize = 1; // domain separation: Poseidon16=1, Poseidon24=2, ExtensionOp>=3

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_A: ColIndex = 1;
pub const POSEIDON_16_COL_B: ColIndex = 2;
pub const POSEIDON_16_COL_RES: ColIndex = 3;
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

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_16_COL_FLAG,
            data: vec![
                BusData::Constant(POSEIDON_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_16_COL_A),
                BusData::Column(POSEIDON_16_COL_B),
                BusData::Column(POSEIDON_16_COL_RES),
            ],
        }
    }

    fn padding_row(&self) -> Vec<F> {
        // depends on null_poseidon_16_hash_ptr (cf lean_prover/trace_gen.rs)
        unreachable!()
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

    pub inputs: [T; WIDTH],
    pub beginning_full_rounds: [[T; WIDTH]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH]; HALF_FINAL_FULL_ROUNDS - 1],
    pub outputs: [T; WIDTH / 2],
}

fn eval_poseidon1_16<AB: AirBuilder>(builder: &mut AB, local: &Poseidon1Cols16<AB::IF>) {
    let mut state: [_; WIDTH] = local.inputs;

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
        add_koala_bear(s, c);
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
            add_koala_bear(&mut state[0], scalar_rc[round]);
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
    state: &mut [AB::IF; WIDTH],
    post_full_round: &[AB::IF; WIDTH],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_16(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_16(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(*state_i, *post_i);
        *state_i = *post_i;
    }
}

#[inline]
fn eval_last_2_full_rounds_16<AB: AirBuilder>(
    initial_state: &[AB::IF; WIDTH],
    state: &mut [AB::IF; WIDTH],
    outputs: &[AB::IF; WIDTH / 2],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_16(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_16(state);
    // add inputs to outputs (for compression)
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += *init_state_i;
    }
    for (state_i, output_i) in state.iter_mut().zip(outputs) {
        builder.assert_eq(*state_i, *output_i);
        *state_i = *output_i;
    }
}

const MDS_CIRC_COL_CANONICAL: [F; 16] =
    KoalaBear::new_array([1, 3, 13, 22, 67, 2, 15, 63, 101, 1, 2, 17, 11, 1, 51, 1]);

#[inline]
fn mds_karatsuba_air_16<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH]) {
    let input = *state;
    let mut output = [A::ZERO; WIDTH];
    conv_air::<A, 16, 8>(
        input,
        MDS_CIRC_COL_CANONICAL,
        &mut output,
        conv8_air::<A>,
        negacyclic_conv8_air::<A>,
    );
    *state = output;
}

#[inline(always)]
fn parity_dot_air<A: PrimeCharacteristicRing + 'static, const N: usize>(lhs: [A; N], rhs: [F; N]) -> A {
    let mut acc = mul_koala_bear(lhs[0], rhs[0]);
    for i in 1..N {
        acc += mul_koala_bear(lhs[i], rhs[i]);
    }
    acc
}

#[inline(always)]
fn conv4_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 4], rhs: [F; 4], output: &mut [A]) {
    let u_p = [lhs[0] + lhs[2], lhs[1] + lhs[3]];
    let u_m = [lhs[0] - lhs[2], lhs[1] - lhs[3]];
    let v_p = [rhs[0] + rhs[2], rhs[1] + rhs[3]];
    let v_m = [rhs[0] - rhs[2], rhs[1] - rhs[3]];
    output[0] = parity_dot_air(u_m, [v_m[0], -v_m[1]]);
    output[1] = parity_dot_air(u_m, [v_m[1], v_m[0]]);
    output[2] = parity_dot_air(u_p, v_p);
    output[3] = parity_dot_air(u_p, [v_p[1], v_p[0]]);
    output[0] += output[2];
    output[1] += output[3];
    output[0] = output[0].halve();
    output[1] = output[1].halve();
    output[2] -= output[0];
    output[3] -= output[1];
}

#[inline(always)]
fn negacyclic_conv4_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 4], rhs: [F; 4], output: &mut [A]) {
    output[0] = parity_dot_air(lhs, [rhs[0], -rhs[3], -rhs[2], -rhs[1]]);
    output[1] = parity_dot_air(lhs, [rhs[1], rhs[0], -rhs[3], -rhs[2]]);
    output[2] = parity_dot_air(lhs, [rhs[2], rhs[1], rhs[0], -rhs[3]]);
    output[3] = parity_dot_air(lhs, [rhs[3], rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn conv_air<A: PrimeCharacteristicRing + 'static, const N: usize, const H: usize>(
    lhs: [A; N],
    rhs: [F; N],
    output: &mut [A],
    inner_conv: fn([A; H], [F; H], &mut [A]),
    inner_neg: fn([A; H], [F; H], &mut [A]),
) {
    let mut lp = [A::ZERO; H];
    let mut ln = [A::ZERO; H];
    let mut rp = [F::ZERO; H];
    let mut rn = [F::ZERO; H];
    for i in 0..H {
        lp[i] = lhs[i] + lhs[i + H];
        ln[i] = lhs[i] - lhs[i + H];
        rp[i] = rhs[i] + rhs[i + H];
        rn[i] = rhs[i] - rhs[i + H];
    }
    let (left, right) = output.split_at_mut(H);
    inner_neg(ln, rn, left);
    inner_conv(lp, rp, right);
    for i in 0..H {
        left[i] += right[i];
        left[i] = left[i].halve();
        right[i] -= left[i];
    }
}

#[inline(always)]
fn negacyclic_conv_air<A: PrimeCharacteristicRing + 'static, const N: usize, const H: usize>(
    lhs: [A; N],
    rhs: [F; N],
    output: &mut [A],
    inner_neg: fn([A; H], [F; H], &mut [A]),
) {
    let mut le = [A::ZERO; H];
    let mut lo = [A::ZERO; H];
    let mut ls = [A::ZERO; H];
    let mut re = [F::ZERO; H];
    let mut ro = [F::ZERO; H];
    let mut rs = [F::ZERO; H];
    for i in 0..H {
        le[i] = lhs[2 * i];
        lo[i] = lhs[2 * i + 1];
        ls[i] = le[i] + lo[i];
        re[i] = rhs[2 * i];
        ro[i] = rhs[2 * i + 1];
        rs[i] = re[i] + ro[i];
    }
    let mut es = [A::ZERO; H];
    let (left, right) = output.split_at_mut(H);
    inner_neg(le, re, &mut es);
    inner_neg(lo, ro, left);
    inner_neg(ls, rs, right);
    right[0] -= es[0] + left[0];
    es[0] -= left[H - 1];
    for i in 1..H {
        right[i] -= es[i] + left[i];
        es[i] += left[i - 1];
    }
    for i in 0..H {
        output[2 * i] = es[i];
        output[2 * i + 1] = output[i + H];
    }
}

fn conv8_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 8], rhs: [F; 8], output: &mut [A]) {
    conv_air(lhs, rhs, output, conv4_air::<A>, negacyclic_conv4_air::<A>);
}

fn negacyclic_conv8_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 8], rhs: [F; 8], output: &mut [A]) {
    negacyclic_conv_air(lhs, rhs, output, negacyclic_conv4_air::<A>);
}

#[inline]
fn dense_mat_vec_air_16<A: PrimeCharacteristicRing + 'static>(mat: &[[F; 16]; 16], state: &mut [A; WIDTH]) {
    let input = *state;
    for i in 0..WIDTH {
        let mut acc = A::ZERO;
        for j in 0..WIDTH {
            acc += mul_koala_bear(input[j], mat[i][j]);
        }
        state[i] = acc;
    }
}

#[inline]
fn sparse_mat_air_16<A: PrimeCharacteristicRing + 'static>(
    state: &mut [A; WIDTH],
    first_row: &[F; WIDTH],
    v: &[F; WIDTH],
) {
    let old_s0 = state[0];
    let mut new_s0 = A::ZERO;
    for j in 0..WIDTH {
        new_s0 += mul_koala_bear(state[j], first_row[j]);
    }
    state[0] = new_s0;
    for i in 1..WIDTH {
        state[i] += mul_koala_bear(old_s0, v[i - 1]);
    }
}

#[inline(always)]
pub(super) fn add_koala_bear<A: 'static>(a: &mut A, value: F) {
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
        unreachable!()
    }
}

#[inline(always)]
pub(super) fn mul_koala_bear<A: PrimeCharacteristicRing + 'static>(a: A, value: F) -> A {
    if TypeId::of::<A>() == TypeId::of::<F>() {
        let r = *unsafe { std::mem::transmute::<&A, &F>(&a) } * value;
        unsafe { std::mem::transmute_copy::<F, A>(&r) }
    } else if TypeId::of::<A>() == TypeId::of::<EF>() {
        let r = *unsafe { std::mem::transmute::<&A, &EF>(&a) } * value;
        unsafe { std::mem::transmute_copy::<EF, A>(&r) }
    } else if TypeId::of::<A>() == TypeId::of::<FPacking<F>>() {
        let r = *unsafe { std::mem::transmute::<&A, &FPacking<F>>(&a) } * value;
        unsafe { std::mem::transmute_copy::<FPacking<F>, A>(&r) }
    } else if TypeId::of::<A>() == TypeId::of::<EFPacking<EF>>() {
        let r = *unsafe { std::mem::transmute::<&A, &EFPacking<EF>>(&a) } * FPacking::<F>::from(value);
        unsafe { std::mem::transmute_copy::<EFPacking<EF>, A>(&r) }
    } else if TypeId::of::<A>() == TypeId::of::<SymbolicExpression<KoalaBear>>() {
        let r = *unsafe { std::mem::transmute::<&A, &SymbolicExpression<KoalaBear>>(&a) } * value;
        unsafe { std::mem::transmute_copy::<SymbolicExpression<KoalaBear>, A>(&r) }
    } else {
        unreachable!()
    }
}
