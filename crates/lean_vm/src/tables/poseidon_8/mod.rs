use crate::*;
use crate::execution::memory::MemoryAccess;
use backend::*;
use utils::{ToUsize, poseidon8_compress};

// TODO(goldilocks-migration): this AIR is currently a soundness stub.
//
// The KoalaBear predecessor implemented Poseidon1 width-16 as an AIR with a
// sparse-matrix factorization for the partial rounds, an `x^3` S-box (degree-3
// compliant with `degree_air = 3`), and tight column packing.
//
// Goldilocks Poseidon1 is width-8 with `x^7` S-box and 22 partial rounds; the
// sbox alone needs witness decomposition (`y2 = x*x`, `y4 = y2*y2`, `y7 = x*y2*y4`)
// to fit under degree 3. That's a fresh column layout and gate algebra — out of
// scope for this migration pass.
//
// The stub below keeps the I/O columns (flag, index_a, index_b, index_res,
// inputs[8], outputs[4]) and the memory lookups + bus, so callers from
// `execute` and the verifier still wire up. The permutation itself is *not*
// constrained — the prover commits the correct `poseidon8_compress` output
// via trace generation, and the verifier accepts it because no gate rejects a
// mismatch. **This is unsound and must be replaced** before shipping.

mod trace_gen;
pub use trace_gen::fill_trace_poseidon_8;

pub(super) const WIDTH: usize = 8;
pub(super) const DIGEST: usize = DIGEST_LEN; // 4

pub const POSEIDON_PRECOMPILE_DATA: usize = 1; // domain separation: Poseidon8=1, ExtensionOp>=8

pub const POSEIDON_8_COL_FLAG: ColIndex = 0;
pub const POSEIDON_8_COL_INDEX_INPUT_LEFT: ColIndex = 1;
pub const POSEIDON_8_COL_INDEX_INPUT_RIGHT: ColIndex = 2;
pub const POSEIDON_8_COL_INDEX_INPUT_RES: ColIndex = 3;
pub const POSEIDON_8_COL_INPUT_START: ColIndex = 4;
pub const POSEIDON_8_COL_OUTPUT_START: ColIndex = POSEIDON_8_COL_INPUT_START + WIDTH;

// Legacy aliases used by other tables/compiler code that still refers to the
// KoalaBear-era names. Keeping them as shims keeps the diff small.
pub const POSEIDON_16_COL_FLAG: ColIndex = POSEIDON_8_COL_FLAG;
pub const POSEIDON_16_COL_INDEX_INPUT_LEFT: ColIndex = POSEIDON_8_COL_INDEX_INPUT_LEFT;
pub const POSEIDON_16_COL_INDEX_INPUT_RIGHT: ColIndex = POSEIDON_8_COL_INDEX_INPUT_RIGHT;
pub const POSEIDON_16_COL_INDEX_INPUT_RES: ColIndex = POSEIDON_8_COL_INDEX_INPUT_RES;
pub const POSEIDON_16_COL_INPUT_START: ColIndex = POSEIDON_8_COL_INPUT_START;

pub const POSEIDON8_NAME: &str = "poseidon8_compress";

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon8Precompile<const BUS: bool>;

impl<const BUS: bool> TableT for Poseidon8Precompile<BUS> {
    fn name(&self) -> &'static str {
        POSEIDON8_NAME
    }

    fn table(&self) -> Table {
        Table::poseidon8()
    }

    fn lookups(&self) -> Vec<LookupIntoMemory> {
        vec![
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_LEFT,
                values: (POSEIDON_8_COL_INPUT_START..POSEIDON_8_COL_INPUT_START + DIGEST).collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RIGHT,
                values: (POSEIDON_8_COL_INPUT_START + DIGEST..POSEIDON_8_COL_INPUT_START + DIGEST * 2)
                    .collect(),
            },
            LookupIntoMemory {
                index: POSEIDON_8_COL_INDEX_INPUT_RES,
                values: (POSEIDON_8_COL_OUTPUT_START..POSEIDON_8_COL_OUTPUT_START + DIGEST).collect(),
            },
        ]
    }

    fn bus(&self) -> Bus {
        Bus {
            direction: BusDirection::Pull,
            selector: POSEIDON_8_COL_FLAG,
            data: vec![
                BusData::Constant(POSEIDON_PRECOMPILE_DATA),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_LEFT),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RIGHT),
                BusData::Column(POSEIDON_8_COL_INDEX_INPUT_RES),
            ],
        }
    }

    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; num_cols_poseidon_8()];
        row[POSEIDON_8_COL_FLAG] = F::ZERO;
        row[POSEIDON_8_COL_INDEX_INPUT_LEFT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_INDEX_INPUT_RIGHT] = F::from_usize(zero_vec_ptr);
        row[POSEIDON_8_COL_INDEX_INPUT_RES] = F::from_usize(null_hash_ptr);
        // inputs stay zero. outputs = poseidon8_compress(0) — truncated to DIGEST.
        let out = poseidon8_compress([F::ZERO; WIDTH]);
        for (i, v) in out.iter().enumerate() {
            row[POSEIDON_8_COL_OUTPUT_START + i] = *v;
        }
        row
    }

    #[inline(always)]
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        _: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        let trace = ctx.traces.get_mut(&self.table()).unwrap();

        let arg0 = ctx.memory.get_slice(arg_a.to_usize(), DIGEST)?;
        let arg1 = ctx.memory.get_slice(arg_b.to_usize(), DIGEST)?;

        let mut input = [F::ZERO; WIDTH];
        input[..DIGEST].copy_from_slice(&arg0);
        input[DIGEST..].copy_from_slice(&arg1);

        let output = poseidon8_compress(input);

        let res_a: [F; DIGEST] = output;

        ctx.memory.set_slice(index_res_a.to_usize(), &res_a)?;

        trace.columns[POSEIDON_8_COL_FLAG].push(F::ONE);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_LEFT].push(arg_a);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RIGHT].push(arg_b);
        trace.columns[POSEIDON_8_COL_INDEX_INPUT_RES].push(index_res_a);
        for (i, value) in input.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_INPUT_START + i].push(*value);
        }
        for (i, value) in output.iter().enumerate() {
            trace.columns[POSEIDON_8_COL_OUTPUT_START + i].push(*value);
        }

        Ok(())
    }
}

impl<const BUS: bool> Air for Poseidon8Precompile<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns(&self) -> usize {
        num_cols_poseidon_8()
    }
    fn degree_air(&self) -> usize {
        3
    }
    fn down_column_indexes(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        // Only the boolean flag gate, plus the bus / declared values.
        1 + BUS as usize
    }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up();
        let flag = up[POSEIDON_8_COL_FLAG];
        let index_a = up[POSEIDON_8_COL_INDEX_INPUT_LEFT];
        let index_b = up[POSEIDON_8_COL_INDEX_INPUT_RIGHT];
        let index_res = up[POSEIDON_8_COL_INDEX_INPUT_RES];

        if BUS {
            builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
                extra_data,
                flag,
                &[
                    AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                    index_a,
                    index_b,
                    index_res,
                ],
            ));
        } else {
            builder.declare_values(std::slice::from_ref(&flag));
            builder.declare_values(&[
                AB::IF::from_usize(POSEIDON_PRECOMPILE_DATA),
                index_a,
                index_b,
                index_res,
            ]);
        }

        builder.assert_bool(flag);

        // TODO(goldilocks-migration): constrain outputs to equal
        // `poseidon8_compress([inputs[0..8]])`. Currently unconstrained — the
        // prover is trusted to fill correct outputs via trace generation.
    }
}

pub const fn num_cols_poseidon_8() -> usize {
    // flag + 3 indices + 8 inputs + 4 outputs
    4 + WIDTH + DIGEST_LEN
}
