use std::array;

use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::{ToUsize, get_poseidon_16_of_zero, poseidon16_permute};

const POSEIDON_16_DEFAULT_COMPRESSION: bool = true;

const POSEIDON_16_COL_FLAG: ColIndex = 0;
const POSEIDON_16_COL_INDEX_RES: ColIndex = 1;
const POSEIDON_16_COL_INDEX_RES_BIS: ColIndex = 2; // = if compressed { 0 } else { POSEIDON_16_COL_INDEX_RES + 1 }
pub const POSEIDON_16_COL_COMPRESSION: ColIndex = 3;
const POSEIDON_16_COL_INDEX_A: ColIndex = 4;
const POSEIDON_16_COL_INDEX_B: ColIndex = 5;
pub const POSEIDON_16_COL_INDEX_INPUT_START: ColIndex = 6;
const POSEIDON_16_COL_INDEX_OUTPUT_START: ColIndex = POSEIDON_16_COL_INDEX_INPUT_START + 16;
// intermediate columns ("commited cubes") are not handled here

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16Precompile;

impl TableT for Poseidon16Precompile {
    fn name(&self) -> &'static str {
        "poseidon16"
    }

    fn identifier(&self) -> Table {
        Table::poseidon16()
    }

    fn n_columns_f_total(&self) -> usize {
        6 + 16 * 2
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        vec![
            POSEIDON_16_COL_FLAG,
            POSEIDON_16_COL_INDEX_RES,
            POSEIDON_16_COL_INDEX_RES_BIS,
            POSEIDON_16_COL_COMPRESSION,
            POSEIDON_16_COL_INDEX_A,
            POSEIDON_16_COL_INDEX_B,
        ] // (committed cubes are handled elsewhere)
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        vec![]
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_A,
                values: array::from_fn(|i| POSEIDON_16_COL_INDEX_INPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_B,
                values: array::from_fn(|i| POSEIDON_16_COL_INDEX_INPUT_START + VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_RES,
                values: array::from_fn(|i| POSEIDON_16_COL_INDEX_OUTPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_16_COL_INDEX_RES_BIS,
                values: array::from_fn(|i| POSEIDON_16_COL_INDEX_OUTPUT_START + VECTOR_LEN + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: POSEIDON_16_COL_FLAG,
            data: vec![
                POSEIDON_16_COL_INDEX_A,
                POSEIDON_16_COL_INDEX_B,
                POSEIDON_16_COL_INDEX_RES,
                POSEIDON_16_COL_COMPRESSION,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        let mut poseidon_of_zero = *get_poseidon_16_of_zero();
        if POSEIDON_16_DEFAULT_COMPRESSION {
            poseidon_of_zero[8..].fill(F::ZERO);
        }
        [
            vec![
                F::ZERO,
                F::from_usize(POSEIDON_16_NULL_HASH_PTR),
                F::from_usize(if POSEIDON_16_DEFAULT_COMPRESSION {
                    ZERO_VEC_PTR
                } else {
                    1 + POSEIDON_16_NULL_HASH_PTR
                }),
                F::from_bool(POSEIDON_16_DEFAULT_COMPRESSION),
                F::from_usize(ZERO_VEC_PTR),
                F::from_usize(ZERO_VEC_PTR),
            ],
            vec![F::ZERO; 16],
            poseidon_of_zero.to_vec(),
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(
        &self,
        arg_a: F,
        arg_b: F,
        index_res_a: F,
        is_compression: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(is_compression == 0 || is_compression == 1);
        let is_compression = is_compression == 1;
        let trace = ctx.traces.get_mut(&self.identifier()).unwrap();

        let arg0 = ctx.memory.get_vector(arg_a.to_usize())?;
        let arg1 = ctx.memory.get_vector(arg_b.to_usize())?;

        let mut input = [F::ZERO; VECTOR_LEN * 2];
        input[..VECTOR_LEN].copy_from_slice(&arg0);
        input[VECTOR_LEN..].copy_from_slice(&arg1);

        let output = match ctx.poseidon16_precomputed.get(*ctx.n_poseidon16_precomputed_used) {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon16_precomputed_used += 1;
                precomputed.1
            }
            _ => poseidon16_permute(input),
        };

        let res_a: [F; VECTOR_LEN] = output[..VECTOR_LEN].try_into().unwrap();
        let (index_res_b, res_b): (F, [F; VECTOR_LEN]) = if is_compression {
            (F::from_usize(ZERO_VEC_PTR), [F::ZERO; VECTOR_LEN])
        } else {
            (index_res_a + F::ONE, output[VECTOR_LEN..].try_into().unwrap())
        };

        ctx.memory.set_vector(index_res_a.to_usize(), res_a)?;
        ctx.memory.set_vector(index_res_b.to_usize(), res_b)?;

        trace.base[POSEIDON_16_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_16_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_16_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_16_COL_INDEX_RES].push(index_res_a);
        trace.base[POSEIDON_16_COL_INDEX_RES_BIS].push(index_res_b);
        trace.base[POSEIDON_16_COL_COMPRESSION].push(F::from_bool(is_compression));
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_16_COL_INDEX_INPUT_START + i].push(*value);
        }
        for (i, value) in res_a.iter().enumerate() {
            trace.base[POSEIDON_16_COL_INDEX_OUTPUT_START + i].push(*value);
        }
        for (i, value) in res_b.iter().enumerate() {
            trace.base[POSEIDON_16_COL_INDEX_OUTPUT_START + 8 + i].push(*value);
        }
        Ok(())
    }
}

impl Air for Poseidon16Precompile {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        6
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        4
    }
    fn eval<AB: p3_air::AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let flag = up[POSEIDON_16_COL_FLAG].clone();
        let index_res = up[POSEIDON_16_COL_INDEX_RES].clone();
        let index_res_bis = up[POSEIDON_16_COL_INDEX_RES_BIS].clone();
        let compression = up[POSEIDON_16_COL_COMPRESSION].clone();
        let index_a = up[POSEIDON_16_COL_INDEX_A].clone();
        let index_b = up[POSEIDON_16_COL_INDEX_B].clone();

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            index_a.clone(),
            index_b.clone(),
            index_res.clone(),
            compression.clone(),
        ));

        builder.assert_bool(flag.clone());
        builder.assert_bool(compression.clone());
        builder.assert_eq(index_res_bis, (index_res + AB::F::ONE) * (AB::F::ONE - compression));
    }
}
