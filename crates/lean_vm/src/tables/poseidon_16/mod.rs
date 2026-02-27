use crate::*;
use backend::*;
use poseidon_gkr::{POSEIDON_16_GKR_START, POSEIDON_16_N_GKR_COLS, POSEIDON_16_N_TOTAL_COLS};
use utils::{ToUsize, poseidon16_compress};

pub(super) const WIDTH: usize = 16;

pub const POSEIDON_PRECOMPILE_DATA: usize = 1; // domain separation between Poseidon / ExtensionOp precompiles

pub const POSEIDON_16_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_COL_A: ColIndex = 1;
pub const POSEIDON_16_COL_B: ColIndex = 2;
pub const POSEIDON_16_COL_RES: ColIndex = 3;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_16_COL_OUTPUT_START: ColIndex = POSEIDON_16_GKR_START + POSEIDON_16_N_GKR_COLS; // 484

/// Number of AIR columns (flag + 3 addresses). Inputs are committed but not AIR-constrained.
pub const N_AIR_COLS_P16: usize = 4;

/// Committed columns: 4 AIR + 16 inputs
pub const N_COMMITTED_COLS_P16: usize = POSEIDON_16_COL_INPUT_START + WIDTH; // 4 + 16 = 20

/// including GKR layers (not committed)
pub const N_TOTAL_COLS_P16: usize = POSEIDON_16_N_TOTAL_COLS; // 492

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon16Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon16"
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
        let mut row = vec![F::ZERO; N_TOTAL_COLS_P16];
        row[1] = F::from_usize(ZERO_VEC_PTR);
        row[2] = F::from_usize(ZERO_VEC_PTR);
        row[3] = F::from_usize(POSEIDON_16_NULL_HASH_PTR);
        // GKR layers are filled by fill_poseidon_trace after padding
        row
    }

    fn n_columns_total(&self) -> usize {
        N_TOTAL_COLS_P16
    }

    fn n_committed_columns(&self) -> usize {
        N_COMMITTED_COLS_P16
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

        // the rest of the trace (GKR layers) is filled at the end of execution (for parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon16Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        N_AIR_COLS_P16
    }
    fn degree_air(&self) -> usize {
        2
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        BUS as usize + 1
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up();
        let flag = up[POSEIDON_16_COL_FLAG].clone();
        let index_a = up[POSEIDON_16_COL_A].clone();
        let index_b = up[POSEIDON_16_COL_B].clone();
        let index_res = up[POSEIDON_16_COL_RES].clone();

        // Bus data: [POSEIDON_PRECOMPILE_DATA (constant), a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag.clone(),
                &[AB::F::from_usize(POSEIDON_PRECOMPILE_DATA), index_a, index_b, index_res],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[AB::F::from_usize(POSEIDON_PRECOMPILE_DATA), index_a, index_b, index_res]);
        }

        builder.assert_bool(flag);
    }
}
