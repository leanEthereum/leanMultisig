use crate::*;
use backend::*;
use poseidon_gkr::{POSEIDON_24_GKR_START, POSEIDON_24_N_GKR_COLS, POSEIDON_24_N_TOTAL_COLS};
use utils::{ToUsize, poseidon24_compress};

pub(super) const WIDTH_24: usize = 24;

pub const POSEIDON_24_PRECOMPILE_DATA: usize = 2; // domain separation: Poseidon16=1, Poseidon24=2, ExtensionOp>=3

pub const POSEIDON_24_INPUT_LEFT_SIZE: usize = 9;
pub const POSEIDON_24_INPUT_RIGHT_SIZE: usize = 15;
pub const POSEIDON_24_OUTPUT_SIZE: usize = 9;

pub const POSEIDON_24_COL_FLAG: ColIndex = 0;
pub const POSEIDON_24_COL_A: ColIndex = 1;
pub const POSEIDON_24_COL_B: ColIndex = 2;
pub const POSEIDON_24_COL_RES: ColIndex = 3;
pub const POSEIDON_24_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_24_COL_OUTPUT_START: ColIndex = POSEIDON_24_GKR_START + POSEIDON_24_N_GKR_COLS;

/// Number of AIR columns (flag + 3 addresses). Inputs are committed but not AIR-constrained.
pub const N_AIR_COLS_P24: usize = 4;

/// Committed columns: 4 AIR + 24 inputs
pub const N_COMMITTED_COLS_P24: usize = POSEIDON_24_COL_INPUT_START + WIDTH_24; // 4 + 24 = 28

/// including GKR layers (not committed)
pub const N_TOTAL_COLS_P24: usize = POSEIDON_24_N_TOTAL_COLS;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon24Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon24Precompile<BUS> {
    fn name(&self) -> &'static str {
        "poseidon24"
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

    fn n_columns_total(&self) -> usize {
        N_TOTAL_COLS_P24
    }

    fn n_committed_columns(&self) -> usize {
        N_COMMITTED_COLS_P24
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

        let output = poseidon24_compress(input); // TODO preprocess with Packing + Parralelism

        let res_a: [F; POSEIDON_24_OUTPUT_SIZE] = output[..POSEIDON_24_OUTPUT_SIZE].try_into().unwrap();

        ctx.memory.set_slice(index_res_a.to_usize(), &res_a)?;

        trace.base[POSEIDON_24_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_24_COL_A].push(arg_a);
        trace.base[POSEIDON_24_COL_B].push(arg_b);
        trace.base[POSEIDON_24_COL_RES].push(index_res_a);
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_24_COL_INPUT_START + i].push(*value);
        }

        // the rest of the trace (GKR layers) is filled at the end of execution (for parallelism + SIMD)

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon24Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        N_AIR_COLS_P24
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
        let flag = up[POSEIDON_24_COL_FLAG];
        let index_a = up[POSEIDON_24_COL_A];
        let index_b = up[POSEIDON_24_COL_B];
        let index_res = up[POSEIDON_24_COL_RES];

        // Bus data: [POSEIDON_24_PRECOMPILE_DATA (constant), a, b, res]
        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag,
                &[
                    AB::IF::from_usize(POSEIDON_24_PRECOMPILE_DATA),
                    index_a,
                    index_b,
                    index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[
                AB::IF::from_usize(POSEIDON_24_PRECOMPILE_DATA),
                index_a,
                index_b,
                index_res,
            ]);
        }

        builder.assert_bool(flag);
    }
}

pub fn default_poseidon_24_row(null_hash_ptr: usize) -> Vec<F> {
    let mut row = vec![F::ZERO; N_TOTAL_COLS_P24];
    row[1] = F::from_usize(ZERO_VEC_PTR);
    row[2] = F::from_usize(ZERO_VEC_PTR);
    row[3] = F::from_usize(null_hash_ptr);
    // GKR layers are filled by fill_poseidon_24_trace after padding
    row
}
