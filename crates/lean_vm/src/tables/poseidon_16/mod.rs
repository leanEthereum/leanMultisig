use std::any::TypeId;

use crate::*;
use crate::{execution::memory::MemoryAccess, tables::poseidon_16::trace_gen::generate_trace_rows_for_perm};
use backend::*;
use utils::{ToUsize, poseidon16_compress};

/// Dispatch `mds_circ_16` through concrete types.
/// For `SymbolicExpression` we use the dense form so the zkDSL generator can
/// emit `dot_product_be` precompile calls instead of Karatsuba arithmetic.
#[inline(always)]
fn mds_air_16<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH]) {
    if TypeId::of::<A>() == TypeId::of::<SymbolicExpression<KoalaBear>>() {
        dense_mat_vec_air_16(mds_dense_16(), state);
        return;
    }
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                mds_circ_16::<$t>(unsafe { &mut *(state as *mut [A; WIDTH] as *mut [$t; WIDTH]) });
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
pub use trace_gen::fill_trace_poseidon_16;

pub(super) const WIDTH: usize = 16;
const HALF_INITIAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;
const PARTIAL_ROUNDS: usize = POSEIDON1_PARTIAL_ROUNDS;
const HALF_FINAL_FULL_ROUNDS: usize = POSEIDON1_HALF_FULL_ROUNDS / 2;

/// Encoding of `PRECOMPILE_DATA` for the Poseidon16 precompile:
///
/// ```text
/// precompile_data =
///       POSEIDON_PRECOMPILE_DATA
///     + POSEIDON_HALF_OUTPUT_SHIFT             * flag_half_output
///     + POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT   * flag_hardcoded_left_4
///     + flag_hardcoded_left_4 * POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT * offset_hardcoded
/// ```
///
/// the last multiplication by flag_hardcoded_left_4 is crucial for soundness.
/// - when flag_hardcoded_left_4 = 1, offset_hardcoded is constrained to be < 2^MAX_LOG_MEMORY_SIZE -> no overflow modulo p
/// - but when flag_hardcoded_left_4 = 0, there isnt this constraint, so we need to need to prevent an attacker to use an overflow to "spoof" the precompile_data encoding
pub const POSEIDON_PRECOMPILE_DATA: usize = 1;
pub const POSEIDON_HALF_OUTPUT_SHIFT: usize = 1 << 1;
pub const POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT: usize = 1 << 2;
pub const POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT: usize = 1 << 3;

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = 2;
pub const POSEIDON_16_COL_FLAG_HALF_OUTPUT: ColIndex = 3;
pub const POSEIDON_16_COL_FLAG_HARDCODED_LEFT_4: ColIndex = 4;
pub const POSEIDON_16_COL_OFFSET_HARDCODED: ColIndex = 5;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST: ColIndex = 6;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND: ColIndex = 7;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 8;
pub const POSEIDON_16_COL_OUTPUT_START: ColIndex = num_cols_poseidon_16() - 8;
/// Non-committed columns ("virtual"):
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = num_cols_poseidon_16();
pub const POSEIDON_16_COL_PRECOMPILE_DATA: ColIndex = num_cols_poseidon_16() + 1;

pub const POSEIDON16_NAME: &str = "poseidon16_compress";
pub const POSEIDON16_HALF_NAME: &str = "poseidon16_compress_half";
pub const POSEIDON16_HARDCODED_LEFT_4_NAME: &str = "poseidon16_compress_hardcoded_left_4";
pub const POSEIDON16_HALF_HARDCODED_LEFT_4_NAME: &str = "poseidon16_compress_half_hardcoded_left_4";
pub const HALF_DIGEST_LEN: usize = DIGEST_LEN / 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon16Precompile<BUS> {
    fn name(&self) -> &'static str {
        POSEIDON16_NAME
    }

    fn table(&self) -> Table {
        Table::poseidon16()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST,
                values: (POSEIDON_16_COL_INPUT_START..POSEIDON_16_COL_INPUT_START + HALF_DIGEST_LEN).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND,
                values: (POSEIDON_16_COL_INPUT_START + HALF_DIGEST_LEN..POSEIDON_16_COL_INPUT_START + DIGEST_LEN)
                    .collect(),
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

    fn n_columns_total(&self) -> usize {
        num_cols_total_poseidon_16()
    }

    #[allow(clippy::vec_init_then_push)] // https://github.com/leanEthereum/leanMultisig/issues/198
    fn bus(&self) -> Bus {
        let mut data = Vec::with_capacity(4);
        data.push(BusData::Column(POSEIDON_16_COL_PRECOMPILE_DATA));
        data.push(BusData::Column(POSEIDON_16_COL_INDEX_INPUT_LEFT));
        data.push(BusData::Column(POSEIDON_16_COL_INDEX_INPUT_RIGHT));
        data.push(BusData::Column(POSEIDON_16_COL_INDEX_INPUT_RES));
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_16_COL_FLAG,
            data,
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_total_poseidon_16()];
        let ptrs: Vec<*mut F> = (0..num_cols_poseidon_16())
            .map(|i| unsafe { row.as_mut_ptr().add(i) })
            .collect();

        let perm: &mut Poseidon1Cols16<&mut F> = unsafe { &mut *(ptrs.as_ptr() as *mut Poseidon1Cols16<&mut F>) };
        perm.inputs.iter_mut().for_each(|x| **x = F::ZERO);
        *perm.flag = F::ZERO;
        *perm.index_b = F::from_usize(zero_vec_ptr);
        *perm.index_res = F::from_usize(null_hash_ptr);
        *perm.flag_half_output = F::ZERO;
        *perm.flag_hardcoded_left_4 = F::ZERO;
        *perm.offset_hardcoded = F::ZERO;
        *perm.effective_index_left_first = F::from_usize(zero_vec_ptr);
        *perm.effective_index_left_second = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        // Non-committed columns
        row[POSEIDON_16_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_16_COL_PRECOMPILE_DATA] = F::from_usize(POSEIDON_PRECOMPILE_DATA);

        generate_trace_rows_for_perm(perm);
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let PrecompileCompTimeArgs::Poseidon16 {
            half_output,
            hardcoded_left_4,
        } = args
        else {
            unreachable!("Poseidon16 table called with non-Poseidon16 args");
        };
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_left_4.is_some();
        // Convention:
        //   flag = 0: left input = m[arg_a..arg_a+8] (split as [arg_a..+4], [arg_a+4..+8])
        //   flag = 1: left input = m[offset..offset+4] | m[arg_a..arg_a+4]
        //             (i.e. arg_a now points to a 4-element data digest, and the first 4
        //              elements come from the hardcoded prefix at `offset`)
        let left_first_addr = hardcoded_left_4.unwrap_or(arg_a_usize);
        let left_second_addr = if flag_hardcoded {
            arg_a_usize
        } else {
            arg_a_usize + HALF_DIGEST_LEN
        };
        let arg0_first = ctx.memory.get_slice(left_first_addr, HALF_DIGEST_LEN)?;
        let arg0_second = ctx.memory.get_slice(left_second_addr, HALF_DIGEST_LEN)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST_LEN)?;

        let mut input = [F::ZERO; DIGEST_LEN * 2];
        input[..HALF_DIGEST_LEN].copy_from_slice(&arg0_first);
        input[HALF_DIGEST_LEN..DIGEST_LEN].copy_from_slice(&arg0_second);
        input[DIGEST_LEN..].copy_from_slice(&arg1);

        let output = poseidon16_compress(input);

        if half_output {
            ctx.memory
                .set_slice(index_res_a.to_usize(), &output[..HALF_DIGEST_LEN])?;
        } else {
            ctx.memory.set_slice(index_res_a.to_usize(), &output)?;
        }

        let offset_hardcoded = hardcoded_left_4.unwrap_or(0);

        trace.columns[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RES].push(index_res_a);
        trace.columns[POSEIDON_16_COL_FLAG_HALF_OUTPUT].push(if half_output { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_16_COL_FLAG_HARDCODED_LEFT_4].push(if flag_hardcoded { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_16_COL_OFFSET_HARDCODED].push(F::from_usize(offset_hardcoded));
        trace.columns[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST].push(F::from_usize(left_first_addr));
        trace.columns[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND].push(F::from_usize(left_second_addr));
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_16_COL_INPUT_START + i].push(*value);
        }
        // Non-committed columns
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_LEFT].push(arg_a);
        let precompile_data = POSEIDON_PRECOMPILE_DATA
            + POSEIDON_HALF_OUTPUT_SHIFT * (half_output as usize)
            + POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT * (flag_hardcoded as usize)
            + POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT * offset_hardcoded;
        trace.columns[POSEIDON_16_COL_PRECOMPILE_DATA].push(F::from_usize(precompile_data));

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
        10 // Last 4 output constraints are gated by (1 - half_output), raising degree from 9 to 10
    }
    fn low_degree_air(&self) -> Option<(usize, usize)> {
        // Each partial round contributes one `assert_eq_low` per round (1 S-box / round), of degree 3 (= the "low" degree part)
        Some((3, PARTIAL_ROUNDS))
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 79
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

        let precompile_data_reconstructed = AB::IF::ONE
            + cols.flag_half_output * AB::F::from_usize(POSEIDON_HALF_OUTPUT_SHIFT)
            + cols.flag_hardcoded_left_4 * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT)
            + cols.flag_hardcoded_left_4
                * cols.offset_hardcoded
                * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT);

        // effective_index_left_first = index_a * (1 - flag_hardcoded_left_4) + offset * flag_hardcoded_left_4
        let index_a = cols.effective_index_left_second
            - (AB::IF::ONE - cols.flag_hardcoded_left_4) * AB::F::from_usize(HALF_DIGEST_LEN);

        // Bus data: [precompile_data, a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag,
                &[precompile_data_reconstructed, index_a, cols.index_b, cols.index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag));
            builder.declare_values(&[precompile_data_reconstructed, index_a, cols.index_b, cols.index_res]);
        }

        builder.assert_bool(cols.flag);
        builder.assert_bool(cols.flag_half_output);
        builder.assert_bool(cols.flag_hardcoded_left_4);

        builder.assert_zero(cols.flag_hardcoded_left_4 * (cols.offset_hardcoded - cols.effective_index_left_first));

        eval_poseidon1_16(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon1Cols16<T> {
    pub flag: T,
    pub index_b: T,
    pub index_res: T,
    pub flag_half_output: T,
    pub flag_hardcoded_left_4: T,
    pub offset_hardcoded: T,
    pub effective_index_left_first: T,
    pub effective_index_left_second: T,

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
    builder.low_degree_block(&mut state, |b, state| {
        let state: &mut [AB::IF; WIDTH] = state.try_into().unwrap();

        let frc = poseidon1_sparse_first_round_constants();
        for (s, &c) in state.iter_mut().zip(frc.iter()) {
            add_kb(s, c);
        }
        dense_mat_vec_air_16(poseidon1_sparse_m_i(), state);

        let first_rows = poseidon1_sparse_first_row();
        let v_vecs = poseidon1_sparse_v();
        let scalar_rc = poseidon1_sparse_scalar_round_constants();
        for round in 0..PARTIAL_ROUNDS {
            // S-box on state[0]
            state[0] = state[0].cube();
            b.assert_eq_low(state[0], local.partial_rounds[round]);
            state[0] = local.partial_rounds[round];
            // Scalar round constant (not on last round)
            if round < PARTIAL_ROUNDS - 1 {
                add_kb(&mut state[0], scalar_rc[round]);
            }
            // Sparse matrix: new_s0 = dot(first_row, state), state[i] += old_s0 * v[i-1]
            sparse_mat_air_16(state, &first_rows[round], &v_vecs[round]);
        }
    });

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
        local.flag_half_output,
        builder,
    );
}

pub const fn num_cols_poseidon_16() -> usize {
    size_of::<Poseidon1Cols16<u8>>()
}

pub const fn num_cols_total_poseidon_16() -> usize {
    // +2 for non-committed columns: POSEIDON_16_COL_INDEX_INPUT_LEFT, POSEIDON_16_COL_PRECOMPILE_DATA
    num_cols_poseidon_16() + 2
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
    initial_state: &[AB::IF; WIDTH],
    state: &mut [AB::IF; WIDTH],
    outputs: &[AB::IF; WIDTH / 2],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
    half_output: AB::IF,
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
    for (idx, (state_i, output_i)) in state.iter_mut().zip(outputs).enumerate() {
        if idx < HALF_DIGEST_LEN {
            // First 4 outputs: always constrained
            builder.assert_eq(*state_i, *output_i);
        } else {
            // Last 4 outputs: constrained only when half_output = 0
            let one_minus_half = AB::IF::ONE - half_output;
            builder.assert_zero(one_minus_half * (*state_i - *output_i));
        }
        *state_i = *output_i;
    }
}

#[inline]
fn dense_mat_vec_air_16<A: PrimeCharacteristicRing + 'static>(mat: &[[F; 16]; 16], state: &mut [A; WIDTH]) {
    let input = *state;
    for i in 0..WIDTH {
        let mut acc = A::ZERO;
        for j in 0..WIDTH {
            acc += mul_kb(input[j], mat[i][j]);
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
        new_s0 += mul_kb(state[j], first_row[j]);
    }
    state[0] = new_s0;
    for i in 1..WIDTH {
        state[i] += mul_kb(old_s0, v[i - 1]);
    }
}
