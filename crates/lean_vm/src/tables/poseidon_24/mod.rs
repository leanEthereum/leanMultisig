use std::any::TypeId;

use crate::*;
use backend::*;
use utils::{ToUsize, poseidon24_compress};

mod trace_gen;
pub use trace_gen::default_poseidon_24_row;
pub use trace_gen::fill_trace_poseidon_24;

pub(super) const WIDTH_24: usize = 24;
const HALF_INITIAL_FULL_ROUNDS_24: usize = POSEIDON1_HALF_FULL_ROUNDS_24 / 2;
const PARTIAL_ROUNDS_24: usize = POSEIDON1_PARTIAL_ROUNDS_24;
const HALF_FINAL_FULL_ROUNDS_24: usize = POSEIDON1_HALF_FULL_ROUNDS_24 / 2;

pub const POSEIDON_24_PRECOMPILE_DATA: usize = 2; // domain separation: Poseidon16=1, Poseidon24=2, ExtensionOp>=3

pub const POSEIDON_24_INPUT_LEFT_SIZE: usize = 9;
pub const POSEIDON_24_INPUT_RIGHT_SIZE: usize = 15;
pub const POSEIDON_24_OUTPUT_SIZE: usize = 9;

pub const POSEIDON_24_COL_FLAG: ColIndex = 0;
pub const POSEIDON_24_COL_A: ColIndex = 1;
pub const POSEIDON_24_COL_B: ColIndex = 2;
pub const POSEIDON_24_COL_RES: ColIndex = 3;
pub const POSEIDON_24_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_24_COL_OUTPUT_START: ColIndex = num_cols_poseidon_24() - POSEIDON_24_OUTPUT_SIZE;

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
                index: POSEIDON_24_COL_A,
                values: (POSEIDON_24_COL_INPUT_START..POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_24_COL_B,
                values: (POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE
                    ..POSEIDON_24_COL_INPUT_START + POSEIDON_24_INPUT_LEFT_SIZE + POSEIDON_24_INPUT_RIGHT_SIZE)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_24_COL_RES,
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
                BusData::Constant(POSEIDON_24_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_24_COL_A),
                BusData::Column(POSEIDON_24_COL_B),
                BusData::Column(POSEIDON_24_COL_RES),
            ],
        }
    }

    fn padding_row(&self) -> Vec<F> {
        // depends on null_poseidon_24_hash_ptr (cf lean_prover/trace_gen.rs)
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

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), POSEIDON_24_INPUT_LEFT_SIZE)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), POSEIDON_24_INPUT_RIGHT_SIZE)?;

        let mut input = [F::ZERO; POSEIDON_24_INPUT_LEFT_SIZE + POSEIDON_24_INPUT_RIGHT_SIZE];
        input[..POSEIDON_24_INPUT_LEFT_SIZE].copy_from_slice(&arg0);
        input[POSEIDON_24_INPUT_LEFT_SIZE..].copy_from_slice(&arg1);

        let output = poseidon24_compress(input); // TODO preprocess with Packing + Parallelism

        let res_a: [F; POSEIDON_24_OUTPUT_SIZE] = output[..POSEIDON_24_OUTPUT_SIZE].try_into().unwrap();

        ctx.memory.set_slice(index_res_a.to_usize(), &res_a)?;

        trace.base[POSEIDON_24_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_24_COL_A].push(arg_a);
        trace.base[POSEIDON_24_COL_B].push(arg_b);
        trace.base[POSEIDON_24_COL_RES].push(index_res_a);
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_24_COL_INPUT_START + i].push(*value);
        }

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
        9
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        // 1 bool check + bus + (HALF_INITIAL * WIDTH) + PARTIAL_ROUNDS + ((HALF_FINAL-1) * WIDTH) + OUTPUT_SIZE
        // = 1 + bus + 2*24 + 23 + 1*24 + 9 = 1 + bus + 48 + 23 + 24 + 9 = 1 + bus + 104
        BUS as usize + 105
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

        // Bus data: [POSEIDON_24_PRECOMPILE_DATA (constant), a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[
                    AB::IF::from_usize(POSEIDON_24_PRECOMPILE_DATA),
                    cols.index_a,
                    cols.index_b,
                    cols.index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[
                AB::IF::from_usize(POSEIDON_24_PRECOMPILE_DATA),
                cols.index_a,
                cols.index_b,
                cols.index_res,
            ]);
        }

        builder.assert_bool(cols.flag);

        eval_poseidon1_24(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon1Cols24<T> {
    pub flag: T,
    pub index_a: T,
    pub index_b: T,
    pub index_res: T,

    pub inputs: [T; WIDTH_24],
    pub beginning_full_rounds: [[T; WIDTH_24]; HALF_INITIAL_FULL_ROUNDS_24],
    pub partial_rounds: [T; PARTIAL_ROUNDS_24],
    pub ending_full_rounds: [[T; WIDTH_24]; HALF_FINAL_FULL_ROUNDS_24 - 1],
    pub outputs: [T; POSEIDON_24_OUTPUT_SIZE],
}

fn eval_poseidon1_24<AB: AirBuilder>(builder: &mut AB, local: &Poseidon1Cols24<AB::IF>) {
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
        add_koala_bear_24(s, c);
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
            add_koala_bear_24(&mut state[0], scalar_rc[round]);
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
        add_koala_bear_24(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_24(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear_24(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_24(state);
    for (state_i, post_i) in state.iter_mut().zip(post_full_round) {
        builder.assert_eq(*state_i, *post_i);
        *state_i = *post_i;
    }
}

#[inline]
fn eval_last_2_full_rounds_24<AB: AirBuilder>(
    initial_state: &[AB::IF; WIDTH_24],
    state: &mut [AB::IF; WIDTH_24],
    outputs: &[AB::IF; POSEIDON_24_OUTPUT_SIZE],
    round_constants_1: &[F; WIDTH_24],
    round_constants_2: &[F; WIDTH_24],
    builder: &mut AB,
) {
    for (s, r) in state.iter_mut().zip(round_constants_1.iter()) {
        add_koala_bear_24(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_24(state);
    for (s, r) in state.iter_mut().zip(round_constants_2.iter()) {
        add_koala_bear_24(s, *r);
        *s = s.cube();
    }
    mds_karatsuba_air_24(state);
    // add inputs to outputs (for compression)
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += *init_state_i;
    }
    for (state_i, output_i) in state[..POSEIDON_24_OUTPUT_SIZE].iter_mut().zip(outputs) {
        builder.assert_eq(*state_i, *output_i);
        *state_i = *output_i;
    }
}

// =========================================================================
// AIR-friendly linear algebra for width-24 Karatsuba convolution (3→6→12→24)
// =========================================================================

// MDS circulant column (same canonical values as MDS_CIRC_COL_24 in poseidon1_koalabear_24.rs)
const MDS_CIRC_COL_24_CANONICAL: [F; 24] = KoalaBear::new_array([
    0x2D0AAAAB, 0x0878A07F, 0x17E118F6, 0x5C7790FA, 0x0A6E572C, 0x6BE4DF69, 0x0524C7F2, 0x0C23DC41, 0x3C2C3DBE,
    0x1689DD98, 0x5D57AFC2, 0x2495A71D, 0x68FC71C8, 0x0360405D, 0x26D52A61, 0x3C0F5038, 0x77CDA9E2, 0x729601A7,
    0x18D6F3CA, 0x60703026, 0x6D91A8D5, 0x04ECBEB5, 0x17F5551D, 0x64850517,
]);

#[inline]
fn mds_karatsuba_air_24<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH_24]) {
    let input = *state;
    let mut output = [A::ZERO; WIDTH_24];
    conv_air_24::<A, 24, 12>(
        input,
        MDS_CIRC_COL_24_CANONICAL,
        &mut output,
        conv12_air::<A>,
        negacyclic_conv12_air::<A>,
    );
    *state = output;
}

#[inline(always)]
fn parity_dot_air_24<A: PrimeCharacteristicRing + 'static, const N: usize>(lhs: [A; N], rhs: [F; N]) -> A {
    let mut acc = mul_koala_bear_24(lhs[0], rhs[0]);
    for i in 1..N {
        acc += mul_koala_bear_24(lhs[i], rhs[i]);
    }
    acc
}

#[inline(always)]
fn conv3_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 3], rhs: [F; 3], output: &mut [A]) {
    output[0] = parity_dot_air_24(lhs, [rhs[0], rhs[2], rhs[1]]);
    output[1] = parity_dot_air_24(lhs, [rhs[1], rhs[0], rhs[2]]);
    output[2] = parity_dot_air_24(lhs, [rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn negacyclic_conv3_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 3], rhs: [F; 3], output: &mut [A]) {
    output[0] = parity_dot_air_24(lhs, [rhs[0], -rhs[2], -rhs[1]]);
    output[1] = parity_dot_air_24(lhs, [rhs[1], rhs[0], -rhs[2]]);
    output[2] = parity_dot_air_24(lhs, [rhs[2], rhs[1], rhs[0]]);
}

#[inline(always)]
fn conv_air_24<A: PrimeCharacteristicRing + 'static, const N: usize, const H: usize>(
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
fn negacyclic_conv_air_24<A: PrimeCharacteristicRing + 'static, const N: usize, const H: usize>(
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

fn conv6_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 6], rhs: [F; 6], output: &mut [A]) {
    conv_air_24(lhs, rhs, output, conv3_air::<A>, negacyclic_conv3_air::<A>);
}

fn negacyclic_conv6_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 6], rhs: [F; 6], output: &mut [A]) {
    negacyclic_conv_air_24(lhs, rhs, output, negacyclic_conv3_air::<A>);
}

fn conv12_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 12], rhs: [F; 12], output: &mut [A]) {
    conv_air_24(lhs, rhs, output, conv6_air::<A>, negacyclic_conv6_air::<A>);
}

fn negacyclic_conv12_air<A: PrimeCharacteristicRing + 'static>(lhs: [A; 12], rhs: [F; 12], output: &mut [A]) {
    negacyclic_conv_air_24(lhs, rhs, output, negacyclic_conv6_air::<A>);
}

#[inline]
fn dense_mat_vec_air_24<A: PrimeCharacteristicRing + 'static>(mat: &[[F; 24]; 24], state: &mut [A; WIDTH_24]) {
    let input = *state;
    for i in 0..WIDTH_24 {
        let mut acc = A::ZERO;
        for j in 0..WIDTH_24 {
            acc += mul_koala_bear_24(input[j], mat[i][j]);
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
        new_s0 += mul_koala_bear_24(state[j], first_row[j]);
    }
    state[0] = new_s0;
    for i in 1..WIDTH_24 {
        state[i] += mul_koala_bear_24(old_s0, v[i - 1]);
    }
}

#[inline(always)]
fn add_koala_bear_24<A: 'static>(a: &mut A, value: F) {
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
fn mul_koala_bear_24<A: PrimeCharacteristicRing + 'static>(a: A, value: F) -> A {
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
