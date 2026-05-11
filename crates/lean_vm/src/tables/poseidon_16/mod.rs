use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::*;
use poseidon_gkr::{POSEIDON_16_N_GKR_COLS, POSEIDON_16_N_GKR_LAYERS};
use utils::{ToUsize, poseidon16_compress};

mod trace_gen;
pub use trace_gen::fill_trace_poseidon_16;

pub(super) const WIDTH: usize = 16;

// `PRECOMPILE_DATA` encoding: see `tables/mod.rs`.
pub const POSEIDON_PRECOMPILE_DATA: usize = 1;
pub const POSEIDON_HALF_OUTPUT_SHIFT: usize = 1 << 1;
pub const POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT: usize = 1 << 2;
pub const POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT: usize = 1 << 3;

// AIR / committed column indices.
pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = 2;
pub const POSEIDON_16_COL_FLAG_HALF_OUTPUT: ColIndex = 3;
pub const POSEIDON_16_COL_FLAG_HARDCODED_LEFT: ColIndex = 4;
pub const POSEIDON_16_COL_OFFSET_LEFT_HARDCODED: ColIndex = 5;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST: ColIndex = 6;
pub const POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND: ColIndex = 7;

/// 8 columns holding the full compressed output (= perm_state + input) for both halves of the digest.
/// These are committed; used by GKR to derive the first 8 output-layer claims and by the AIR to
/// constrain `eff_second` against them in the !half_output case.
pub const POSEIDON_16_COL_COMPRESSED_OUTPUT_START: ColIndex = 8;

/// 4 columns holding the memory residue at `index_res + 4..+8`. These are the actual values that
/// memory contains in that range — for !half_output rows it equals compressed_output[4..8]; for
/// half_output rows the prover may write whatever memory holds.
pub const POSEIDON_16_COL_EFF_SECOND_START: ColIndex = POSEIDON_16_COL_COMPRESSED_OUTPUT_START + DIGEST_LEN;

/// The 16 input columns to the Poseidon permutation.
pub const POSEIDON_16_COL_INPUT_START: ColIndex = POSEIDON_16_COL_EFF_SECOND_START + HALF_DIGEST_LEN;

/// First column index past the last committed column.
pub const POSEIDON_16_N_AIR_COLS: usize = POSEIDON_16_COL_EFF_SECOND_START + HALF_DIGEST_LEN; // 20
pub const POSEIDON_16_N_COMMITTED_COLS: usize = POSEIDON_16_COL_INPUT_START + WIDTH; // 36

/// GKR layer columns start right after the committed columns.
pub const POSEIDON_16_COL_GKR_START: ColIndex = POSEIDON_16_N_COMMITTED_COLS;

/// "OUTPUT_START" in the new layout is the compressed-output area (so that lookups into memory
/// match the public API).  Kept for compatibility with existing prover/trace_gen code.
pub const POSEIDON_16_COL_OUTPUT_START: ColIndex = POSEIDON_16_COL_COMPRESSED_OUTPUT_START;

/// Non-committed ("virtual") columns: filled by execute() so that logup can use them in the bus.
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = POSEIDON_16_COL_GKR_START + POSEIDON_16_N_GKR_COLS;
pub const POSEIDON_16_COL_PRECOMPILE_DATA: ColIndex = POSEIDON_16_COL_INDEX_INPUT_LEFT + 1;

pub const POSEIDON16_NAME: &str = "poseidon16_compress";
pub const POSEIDON16_HALF_NAME: &str = "poseidon16_compress_half";
pub const POSEIDON16_HARDCODED_LEFT_NAME: &str = "poseidon16_compress_hardcoded_left";
pub const POSEIDON16_HALF_HARDCODED_LEFT_NAME: &str = "poseidon16_compress_half_hardcoded_left";
pub const ALL_POSEIDON16_NAMES: [&str; 4] = [
    POSEIDON16_NAME,
    POSEIDON16_HALF_NAME,
    POSEIDON16_HARDCODED_LEFT_NAME,
    POSEIDON16_HALF_HARDCODED_LEFT_NAME,
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
        let res_values: Vec<ColIndex> = (POSEIDON_16_COL_COMPRESSED_OUTPUT_START
            ..POSEIDON_16_COL_COMPRESSED_OUTPUT_START + HALF_DIGEST_LEN)
            .chain(POSEIDON_16_COL_EFF_SECOND_START..POSEIDON_16_COL_EFF_SECOND_START + HALF_DIGEST_LEN)
            .collect();
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
                values: res_values,
            },
        ]
    }

    fn n_columns_total(&self) -> usize {
        num_cols_total_poseidon_16()
    }

    fn n_committed_columns(&self) -> usize {
        POSEIDON_16_N_COMMITTED_COLS
    }

    #[allow(clippy::vec_init_then_push)]
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
        // Inputs are zero (default).
        row[POSEIDON_16_COL_FLAG] = F::ZERO;
        row[POSEIDON_16_COL_INDEX_INPUT_RIGHT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_16_COL_INDEX_INPUT_RES] = F::from_usize(null_hash_ptr);
        row[POSEIDON_16_COL_FLAG_HALF_OUTPUT] = F::ZERO;
        row[POSEIDON_16_COL_FLAG_HARDCODED_LEFT] = F::ZERO;
        row[POSEIDON_16_COL_OFFSET_LEFT_HARDCODED] = F::ZERO;
        row[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND] = F::from_usize(zero_vec_ptr + HALF_DIGEST_LEN);
        // Virtual columns
        row[POSEIDON_16_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_16_COL_PRECOMPILE_DATA] = F::from_usize(POSEIDON_PRECOMPILE_DATA);

        // Compressed output = poseidon(0) (since inputs are zero, perm(0) + 0 = perm(0)).
        // The full poseidon-of-zero result is at memory[null_hash_ptr..+DIGEST_LEN]; we mirror it.
        // (The GKR layer columns are filled later by fill_trace_poseidon_16.)
        let null_hash = utils::get_poseidon_16_of_zero();
        for i in 0..DIGEST_LEN {
            row[POSEIDON_16_COL_COMPRESSED_OUTPUT_START + i] = null_hash[i];
        }
        for i in 0..HALF_DIGEST_LEN {
            row[POSEIDON_16_COL_EFF_SECOND_START + i] = null_hash[HALF_DIGEST_LEN + i];
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
            hardcoded_offset_left,
        } = args
        else {
            unreachable!("Poseidon16 table called with non-Poseidon16 args");
        };
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg_a_usize = arg_a.to_usize();
        let flag_hardcoded = hardcoded_offset_left.is_some();
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

        let output = poseidon16_compress(input);

        // Read the upper-half memory residue BEFORE writing (so half_output rows record the
        // pre-existing memory contents, exactly what the lookup will see).
        let res_addr = index_res_a.to_usize();
        let upper_residue_pre_write = ctx
            .memory
            .get_slice(res_addr + HALF_DIGEST_LEN, HALF_DIGEST_LEN)
            .ok();

        if half_output {
            ctx.memory
                .set_slice(res_addr, &output[..HALF_DIGEST_LEN])?;
        } else {
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
        // Compressed output (always the full poseidon output, regardless of half_output).
        for i in 0..DIGEST_LEN {
            trace.columns[POSEIDON_16_COL_COMPRESSED_OUTPUT_START + i].push(output[i]);
        }
        // eff_second: memory residue at index_res + 4..+8
        //   * !half_output: memory was just written to output[4..8] -> matches compressed_output[4..8]
        //   * half_output : memory unchanged -> upper_residue_pre_write
        for i in 0..HALF_DIGEST_LEN {
            let value = if half_output {
                upper_residue_pre_write
                    .as_ref()
                    .map(|s| s[i])
                    .unwrap_or(F::ZERO)
            } else {
                output[HALF_DIGEST_LEN + i]
            };
            trace.columns[POSEIDON_16_COL_EFF_SECOND_START + i].push(value);
        }
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_16_COL_INPUT_START + i].push(*value);
        }
        // Non-committed virtual columns
        trace.columns[POSEIDON_16_COL_INDEX_INPUT_LEFT].push(arg_a);
        let precompile_data = POSEIDON_PRECOMPILE_DATA
            + POSEIDON_HALF_OUTPUT_SHIFT * (half_output as usize)
            + POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT * (flag_hardcoded as usize)
            + POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT * hardcoded_offset_left_val;
        trace.columns[POSEIDON_16_COL_PRECOMPILE_DATA].push(F::from_usize(precompile_data));

        // GKR layer columns are filled at the end of execution (parallelism + SIMD).

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon16Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        POSEIDON_16_N_AIR_COLS
    }
    fn degree_air(&self) -> usize {
        2
    }
    fn low_degree_air(&self) -> Option<(usize, usize)> {
        None
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        // - bus virtual eq                                                : 1 (only when BUS)
        // - assert_bool(flag_active)                                      : 1
        // - assert_bool(flag_half_output)                                 : 1
        // - assert_bool(flag_hardcoded_left)                              : 1
        // - hardcoded_left * (offset_left - effective_index_left_first)   : 1
        // - (1-hardcoded_left) * (index_a - effective_index_left_first)   : 1
        // - (1 - half_output) * (eff_second[i] - compressed_output[i+4])  : 4
        BUS as usize + 9
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let (
            flag,
            index_b,
            index_res,
            flag_half_output,
            flag_hardcoded_left,
            offset_hardcoded_left,
            eff_left_first,
            eff_left_second,
            eff_second,
            compressed_upper,
        ) = {
            let up = builder.up();
            let eff_second: [AB::IF; HALF_DIGEST_LEN] = std::array::from_fn(|i| up[POSEIDON_16_COL_EFF_SECOND_START + i]);
            let compressed_upper: [AB::IF; HALF_DIGEST_LEN] =
                std::array::from_fn(|i| up[POSEIDON_16_COL_COMPRESSED_OUTPUT_START + HALF_DIGEST_LEN + i]);
            (
                up[POSEIDON_16_COL_FLAG],
                up[POSEIDON_16_COL_INDEX_INPUT_RIGHT],
                up[POSEIDON_16_COL_INDEX_INPUT_RES],
                up[POSEIDON_16_COL_FLAG_HALF_OUTPUT],
                up[POSEIDON_16_COL_FLAG_HARDCODED_LEFT],
                up[POSEIDON_16_COL_OFFSET_LEFT_HARDCODED],
                up[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_FIRST],
                up[POSEIDON_16_COL_EFFECTIVE_INDEX_LEFT_SECOND],
                eff_second,
                compressed_upper,
            )
        };

        let precompile_data_reconstructed = AB::IF::ONE
            + flag_half_output * AB::F::from_usize(POSEIDON_HALF_OUTPUT_SHIFT)
            + flag_hardcoded_left * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_FLAG_SHIFT)
            + flag_hardcoded_left * offset_hardcoded_left * AB::F::from_usize(POSEIDON_HARDCODED_LEFT_4_OFFSET_SHIFT);

        let one_minus_flag_hardcoded_left = AB::IF::ONE - flag_hardcoded_left;
        let index_a = eff_left_second - one_minus_flag_hardcoded_left * AB::F::from_usize(HALF_DIGEST_LEN);

        if BUS {
            builder.assert_zero_ef(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag,
                &[precompile_data_reconstructed, index_a, index_b, index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[precompile_data_reconstructed, index_a, index_b, index_res]);
        }

        builder.assert_bool(flag);
        builder.assert_bool(flag_half_output);
        builder.assert_bool(flag_hardcoded_left);

        builder.assert_zero(flag_hardcoded_left * (offset_hardcoded_left - eff_left_first));
        builder.assert_zero(one_minus_flag_hardcoded_left * (index_a - eff_left_first));

        // (1 - half_output) * (eff_second[i] - compressed_output[i + HALF_DIGEST_LEN]) = 0
        let one_minus_half_output = AB::IF::ONE - flag_half_output;
        for i in 0..HALF_DIGEST_LEN {
            builder.assert_zero(one_minus_half_output * (eff_second[i] - compressed_upper[i]));
        }
    }
}

pub const fn num_cols_poseidon_16() -> usize {
    // AIR-only column count (the "logical" AIR columns the AIR sumcheck touches).
    POSEIDON_16_N_AIR_COLS
}

pub const fn num_cols_total_poseidon_16() -> usize {
    POSEIDON_16_N_COMMITTED_COLS // 36 (committed)
        + POSEIDON_16_N_GKR_COLS // 464 (non-committed GKR layers)
        + 2 // INDEX_INPUT_LEFT + PRECOMPILE_DATA virtual columns
}

const _: () = {
    // Sanity: layer count matches the GKR crate.
    assert!(POSEIDON_16_N_GKR_LAYERS == 29);
};
