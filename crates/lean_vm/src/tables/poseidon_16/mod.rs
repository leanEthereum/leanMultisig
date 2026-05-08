use std::any::TypeId;

use crate::*;
use crate::{execution::memory::MemoryAccess, tables::poseidon_16::trace_gen::generate_trace_rows_for_perm};
use backend::*;
use utils::{ToUsize, poseidon16_compress};

/// Dispatch the circulant MDS multiply through concrete types.
///
/// - `SymbolicExpression`: dense matrix-vector form so the zkDSL generator can
///   emit `dot_product_be` precompile calls instead of Karatsuba arithmetic.
/// - Runtime field types (F, EF, FPacking, EFPacking): FFT-based MDS
///   (`mds_fft_16`, 50 mults) instead of Karatsuba (`mds_circ_16`, 72 mults).
///   Same algebraic result; ~30% fewer mults per call.
#[inline(always)]
fn mds_air_16<A: PrimeCharacteristicRing + 'static>(state: &mut [A; WIDTH]) {
    if TypeId::of::<A>() == TypeId::of::<SymbolicExpression<KoalaBear>>() {
        dense_mat_vec_air_16(mds_dense_16(), state);
        return;
    }
    macro_rules! dispatch {
        ($t:ty) => {
            if TypeId::of::<A>() == TypeId::of::<$t>() {
                mds_fft_16::<$t>(unsafe { &mut *(state as *mut [A; WIDTH] as *mut [$t; WIDTH]) });
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

// `PRECOMPILE_DATA` encoding: see `tables/mod.rs`.
pub const POSEIDON_PRECOMPILE_DATA: usize = 1;
pub const POSEIDON_HALF_OUTPUT_SHIFT: usize = 1 << 1;
pub const POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT: usize = 1 << 2;
pub const POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT: usize = 1 << 3;
// Bit 30 is safely beyond `8 * MAX_LOG_MEMORY_SIZE = 2^29` so it cannot
// alias with `POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT * offset`.
pub const POSEIDON_FULL_OUTPUT_SHIFT: usize = 1 << 30;

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = 2;
pub const POSEIDON_16_COL_FLAG_HALF_OUTPUT: ColIndex = 3;
pub const POSEIDON_16_COL_FLAG_HARDCODED_LEFT: ColIndex = 4;
pub const POSEIDON_16_COL_OFFSET_LEFT_HARDCODED: ColIndex = 5;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST: ColIndex = 6;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND: ColIndex = 7;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 8;
// Layout at end of struct (in field-declaration order):
//   ... outputs (DIGEST_LEN cols) ... flag_full_output (1) ... index_input_res_high (1) ... outputs_high (DIGEST_LEN)
// So OUTPUTS_HIGH_START = num_cols - DIGEST_LEN, INDEX_INPUT_RES_HIGH = num_cols - DIGEST_LEN - 1,
// FLAG_FULL_OUTPUT = num_cols - DIGEST_LEN - 2, OUTPUT_START = num_cols - DIGEST_LEN - 2 - DIGEST_LEN.
pub const POSEIDON_16_COL_OUTPUTS_HIGH_START: ColIndex = num_cols_poseidon_16() - DIGEST_LEN;
pub const POSEIDON_16_COL_INDEX_INPUT_RES_HIGH: ColIndex = POSEIDON_16_COL_OUTPUTS_HIGH_START - 1;
pub const POSEIDON_16_COL_FLAG_FULL_OUTPUT: ColIndex = POSEIDON_16_COL_INDEX_INPUT_RES_HIGH - 1;
pub const POSEIDON_16_COL_OUTPUT_START: ColIndex = POSEIDON_16_COL_FLAG_FULL_OUTPUT - DIGEST_LEN;
/// Non-committed columns ("virtual"):
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = num_cols_poseidon_16();
pub const POSEIDON_16_COL_PRECOMPILE_DATA: ColIndex = num_cols_poseidon_16() + 1;

pub const POSEIDON16_NAME: &str = "poseidon16_compress";
pub const POSEIDON16_HALF_NAME: &str = "poseidon16_compress_half";
pub const POSEIDON16_HARDCODED_LEFT_NAME: &str = "poseidon16_compress_hardcoded_left";
pub const POSEIDON16_HALF_HARDCODED_LEFT_NAME: &str = "poseidon16_compress_half_hardcoded_left";
/// Permute mode: writes ALL 16 perm-output elements (with input feedforward) to memory.
/// Used for MMO sponge leaf hashing where the FULL 16-element state must be chained
/// between rounds to achieve `output_bits/2 = 124`-bit collision security at any rate.
pub const POSEIDON16_PERMUTE_NAME: &str = "poseidon16_permute";
pub const ALL_POSEIDON16_NAMES: [&str; 5] = [
    POSEIDON16_NAME,
    POSEIDON16_HALF_NAME,
    POSEIDON16_HARDCODED_LEFT_NAME,
    POSEIDON16_HALF_HARDCODED_LEFT_NAME,
    POSEIDON16_PERMUTE_NAME,
];
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
            // High-half output lookup (only meaningful in permute mode, but always active).
            // For non-permute rows the trace_gen sets index_input_res_high = zero_vec_ptr and
            // outputs_high = 0, so this lookup checks `m[zero_vec_ptr+i] == 0` (trivially true).
            LookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_INPUT_RES_HIGH,
                values: (POSEIDON_16_COL_OUTPUTS_HIGH_START..POSEIDON_16_COL_OUTPUTS_HIGH_START + DIGEST_LEN).collect(),
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
        *perm.flag_active = F::ZERO;
        *perm.index_b = F::from_usize(zero_vec_ptr);
        *perm.index_res = F::from_usize(null_hash_ptr);
        *perm.flag_half_output = F::ZERO;
        *perm.flag_hardcoded_left = F::ZERO;
        *perm.offset_hardcoded_left = F::ZERO;
        *perm.effective_index_left_first = F::from_usize(zero_vec_ptr);
        *perm.effective_index_left_second = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        *perm.flag_full_output = F::ZERO;
        // Padding rows are non-permute → high-output index points at zero_vec_ptr (a 16-cell zero region).
        *perm.index_input_res_high = F::from_usize(zero_vec_ptr);
        // outputs_high is zeroed by the constraint `(1 - flag_full_output) * outputs_high[i] = 0`;
        // the trace generator below leaves them at F::ZERO via the Vec::new() default.
        // Non-committed columns
        row[POSEIDON_16_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_16_COL_PRECOMPILE_DATA] = F::from_usize(POSEIDON_PRECOMPILE_DATA);

        generate_trace_rows_for_perm(perm);
        // generate_trace_rows_for_perm fills outputs[0..8] with state[i] + inputs[i]; for padding
        // rows inputs are all zero so outputs ≡ Poseidon-16(0) (8 elements). outputs_high however
        // must be zero per the AIR constraint, so explicitly clear it after the perm trace fill.
        for output_high in perm.outputs_high.iter_mut() {
            **output_high = F::ZERO;
        }
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
            full_output,
            hardcoded_offset_left,
        } = args
        else {
            unreachable!("Poseidon16 table called with non-Poseidon16 args");
        };
        debug_assert!(!(half_output && full_output), "half_output and full_output are mutually exclusive");
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
        // Convention:
        //   flag_hardcoded = 0: left input = m[arg_a..arg_a+8] (split as [arg_a..+4], [arg_a+4..+8])
        //   flag_hardcoded = 1: left input = m[offset..offset+4] | m[arg_a..arg_a+4]
        //                   (i.e. arg_a now points to a 4-element data digest, and the first 4
        //                    elements come from the hardcoded prefix at `offset`)
        let left_first_addr = hardcoded_offset_left.unwrap_or(arg_a_usize);
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

        let res_addr = index_res_a.to_usize();
        if full_output {
            // Write all 16 elements (perm output + input feedforward) to memory.
            let full = utils::poseidon16_permute_full(input);
            ctx.memory.set_slice(res_addr, &full)?;
        } else if half_output {
            let output = poseidon16_compress(input);
            ctx.memory.set_slice(res_addr, &output[..HALF_DIGEST_LEN])?;
        } else {
            let output = poseidon16_compress(input);
            ctx.memory.set_slice(res_addr, &output)?;
        }

        let hardcoded_offset_left_val = hardcoded_offset_left.unwrap_or(0);

        trace.columns[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RES].push(index_res_a);
        trace.columns[POSEIDON_16_COL_FLAG_HALF_OUTPUT].push(if half_output { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_16_COL_FLAG_HARDCODED_LEFT].push(if flag_hardcoded { F::ONE } else { F::ZERO });
        trace.columns[POSEIDON_16_COL_OFFSET_LEFT_HARDCODED].push(F::from_usize(hardcoded_offset_left_val));
        trace.columns[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST].push(F::from_usize(left_first_addr));
        trace.columns[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND].push(F::from_usize(left_second_addr));
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_16_COL_INPUT_START + i].push(*value);
        }
        trace.columns[POSEIDON_16_COL_FLAG_FULL_OUTPUT].push(if full_output { F::ONE } else { F::ZERO });
        // index_input_res_high: real address (res+8) when in permute mode; otherwise a placeholder
        // that will be rewritten in lean_prover post-processing to a zero region. Use 0 for now;
        // soundness is maintained because the AIR constraint
        //   `flag_full_output * (index_input_res_high - index_input_res - 8) = 0`
        // only forces the value when permute mode is on.
        let index_high = if full_output { res_addr + DIGEST_LEN } else { 0 };
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_RES_HIGH].push(F::from_usize(index_high));
        // outputs_high columns are filled by trace_gen (perm output high half) for permute rows,
        // and overwritten to zero in lean_prover post-processing for non-permute rows.
        // Non-committed columns
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_LEFT].push(arg_a);
        let precompile_data = POSEIDON_PRECOMPILE_DATA
            + POSEIDON_HALF_OUTPUT_SHIFT * (half_output as usize)
            + POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT * (flag_hardcoded as usize)
            + POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT * hardcoded_offset_left_val
            + POSEIDON_FULL_OUTPUT_SHIFT * (full_output as usize);
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
        // 80 (existing) + 1 (full_output bool) + 1 (full*half mutex) + 1 (high index)
        // + 8 (full * (outputs_high[i] - state - input)) + 8 ((1-full) * outputs_high[i])
        BUS as usize + 80 + 19
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
            + cols.flag_hardcoded_left * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT)
            + cols.flag_hardcoded_left
                * cols.offset_hardcoded_left
                * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT)
            + cols.flag_full_output * AB::F::from_usize(POSEIDON_FULL_OUTPUT_SHIFT);

        // effective_index_left_first = index_a * (1 - flag_hardcoded_left_4) + offset * flag_hardcoded_left_4
        let one_minus_flag_hardcoded_left = AB::IF::ONE - cols.flag_hardcoded_left;
        let index_a =
            cols.effective_index_left_second - one_minus_flag_hardcoded_left * AB::F::from_usize(HALF_DIGEST_LEN);

        // Bus data: [precompile_data, a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                cols.flag_active,
                &[precompile_data_reconstructed, index_a, cols.index_b, cols.index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&cols.flag_active));
            builder.declare_values(&[precompile_data_reconstructed, index_a, cols.index_b, cols.index_res]);
        }

        builder.assert_bool(cols.flag_active);
        builder.assert_bool(cols.flag_half_output);
        builder.assert_bool(cols.flag_hardcoded_left);
        builder.assert_bool(cols.flag_full_output);
        // Mutually exclusive: a row cannot be both half-output and full-output.
        builder.assert_zero(cols.flag_full_output * cols.flag_half_output);
        // When full_output is set, index_input_res_high MUST equal index_res + DIGEST_LEN so that
        // outputs_high lands at m[res+8..res+16]. When full_output is unset, the trace generator
        // is free to set index_input_res_high to any zero-page address; the lookup will check
        // outputs_high (= 0) against m[that_address+i] which is zero by construction.
        builder.assert_zero(
            cols.flag_full_output
                * (cols.index_input_res_high - cols.index_res - AB::F::from_usize(DIGEST_LEN)),
        );

        builder.assert_zero(cols.flag_hardcoded_left * (cols.offset_hardcoded_left - cols.effective_index_left_first));
        builder.assert_zero(one_minus_flag_hardcoded_left * (index_a - cols.effective_index_left_first));

        eval_poseidon1_16(builder, &cols)
    }
}

#[repr(C)]
#[derive(Debug)]
pub(super) struct Poseidon1Cols16<T> {
    pub flag_active: T, // 0 = padding, 1 = active
    pub index_b: T,
    pub index_res: T,
    pub flag_half_output: T,
    pub flag_hardcoded_left: T,
    pub offset_hardcoded_left: T,
    pub effective_index_left_first: T,
    pub effective_index_left_second: T,

    pub inputs: [T; WIDTH],
    pub beginning_full_rounds: [[T; WIDTH]; HALF_INITIAL_FULL_ROUNDS],
    pub partial_rounds: [T; PARTIAL_ROUNDS],
    pub ending_full_rounds: [[T; WIDTH]; HALF_FINAL_FULL_ROUNDS - 1],
    pub outputs: [T; WIDTH / 2],
    /// 1 = expose all 16 perm-output elements (writes outputs_high to m[res+8..res+16]).
    /// Mutually exclusive with flag_half_output.
    pub flag_full_output: T,
    /// Memory address for the high-half outputs. = index_res + DIGEST_LEN when flag_full_output;
    /// otherwise points at zero_vec_ptr (a region pre-filled with zeros) so the lookup is a no-op.
    pub index_input_res_high: T,
    /// High-half perm output (state[8..16] + inputs[8..16]). Constrained when flag_full_output;
    /// forced to zero when not, so the lookup against zero_vec_ptr is trivially satisfied.
    pub outputs_high: [T; WIDTH / 2],
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
        &local.outputs_high,
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS - 1)],
        &final_constants[2 * (HALF_FINAL_FULL_ROUNDS - 1) + 1],
        local.flag_half_output,
        local.flag_full_output,
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
    outputs_high: &[AB::IF; WIDTH / 2],
    round_constants_1: &[F; WIDTH],
    round_constants_2: &[F; WIDTH],
    flag_half_output: AB::IF,
    flag_full_output: AB::IF,
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
    // add inputs to outputs (for compression / MMO feedforward)
    for (state_i, init_state_i) in state.iter_mut().zip(initial_state) {
        *state_i += *init_state_i;
    }
    let one_minus_flag_half_output = AB::IF::ONE - flag_half_output;
    let one_minus_flag_full_output = AB::IF::ONE - flag_full_output;
    // First 8 outputs: existing behavior (always 0..4, gated by half on 4..8).
    for (idx, (state_i, output_i)) in state.iter().take(WIDTH / 2).zip(outputs).enumerate() {
        if idx < HALF_DIGEST_LEN {
            builder.assert_eq(*state_i, *output_i);
        } else {
            builder.assert_zero(one_minus_flag_half_output * (*state_i - *output_i));
        }
    }
    // Outputs_high: constrained to state[8..16] when full_output, else forced to zero.
    for (state_i, output_high_i) in state.iter().skip(WIDTH / 2).zip(outputs_high) {
        builder.assert_zero(flag_full_output * (*state_i - *output_high_i));
        builder.assert_zero(one_minus_flag_full_output * *output_high_i);
    }
    // Mirror the original "advance state to output" so any downstream code sees the canonical state.
    for (idx, output_i) in outputs.iter().enumerate() {
        state[idx] = *output_i;
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
