use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use std::array;
use utils::{ToUsize, get_poseidon_24_of_zero, poseidon24_permute};

const POSEIDON_24_COL_FLAG: ColIndex = 0;
const POSEIDON_24_COL_INDEX_A: ColIndex = 1;
const POSEIDON_24_COL_INDEX_A_BIS: ColIndex = 2;
const POSEIDON_24_COL_INDEX_B: ColIndex = 3;
const POSEIDON_24_COL_INDEX_RES: ColIndex = 4;
pub const POSEIDON_24_COL_INPUT_START: ColIndex = 5;
pub const POSEIDON_24_COL_OUTPUT_START: ColIndex = POSEIDON_24_COL_INPUT_START + 24;
// intermediate columns ("commited cubes") are not handled here

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon24Precompile;

impl TableT for Poseidon24Precompile {
    fn name(&self) -> &'static str {
        "poseidon24"
    }

    fn identifier(&self) -> Table {
        Table::poseidon24()
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
                index: POSEIDON_24_COL_INDEX_A,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_A_BIS,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_B,
                values: array::from_fn(|i| POSEIDON_24_COL_INPUT_START + 2 * VECTOR_LEN + i),
            },
            VectorLookupIntoMemory {
                index: POSEIDON_24_COL_INDEX_RES,
                values: array::from_fn(|i| POSEIDON_24_COL_OUTPUT_START + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: BusSelector::Column(POSEIDON_24_COL_FLAG),
            data: vec![
                POSEIDON_24_COL_INDEX_A,
                POSEIDON_24_COL_INDEX_B,
                POSEIDON_24_COL_INDEX_RES,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![
                F::ZERO,
                F::from_usize(ZERO_VEC_PTR),
                F::from_usize(ZERO_VEC_PTR + 1),
                F::from_usize(ZERO_VEC_PTR),
                F::from_usize(POSEIDON_24_NULL_HASH_PTR),
            ],
            vec![F::ZERO; 24],
            get_poseidon_24_of_zero()[16..].to_vec(),
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
        res: F,
        aux: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert_eq!(aux, 0); // no aux for poseidon24
        let trace = ctx.traces.get_mut(&self.identifier()).unwrap();

        let arg0 = ctx.memory.get_vector(arg_a.to_usize())?;
        let arg1 = ctx.memory.get_vector(1 + arg_a.to_usize())?;
        let arg2 = ctx.memory.get_vector(arg_b.to_usize())?;

        let mut input = [F::ZERO; VECTOR_LEN * 3];
        input[..VECTOR_LEN].copy_from_slice(&arg0);
        input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
        input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

        let output = match ctx.poseidon24_precomputed.get(*ctx.n_poseidon24_precomputed_used) {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon24_precomputed_used += 1;
                precomputed.1
            }
            _ => {
                let output = poseidon24_permute(input);
                output[2 * VECTOR_LEN..].try_into().unwrap()
            }
        };

        ctx.memory.set_vector(res.to_usize(), output)?;

        trace.base[POSEIDON_24_COL_FLAG].push(F::ONE);
        trace.base[POSEIDON_24_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_24_COL_INDEX_A_BIS].push(arg_a + F::ONE);
        trace.base[POSEIDON_24_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_24_COL_INDEX_RES].push(res);
        for (i, value) in input.iter().enumerate() {
            trace.base[POSEIDON_24_COL_INPUT_START + i].push(*value);
        }
        for (i, value) in output.iter().enumerate() {
            trace.base[POSEIDON_24_COL_OUTPUT_START + i].push(*value);
        }

        Ok(())
    }
}

impl Air for Poseidon24Precompile {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        5 + 24 + 8
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
        let flag = up[POSEIDON_24_COL_FLAG].clone();
        let index_res = up[POSEIDON_24_COL_INDEX_RES].clone();
        let index_input_a = up[POSEIDON_24_COL_INDEX_A].clone();
        let index_input_a_bis = up[POSEIDON_24_COL_INDEX_A_BIS].clone();
        let index_b = up[POSEIDON_24_COL_INDEX_B].clone();

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            &[index_input_a.clone(), index_b, index_res, AB::F::ZERO],
        ));

        builder.assert_bool(flag);
        builder.assert_eq(index_input_a_bis, index_input_a + AB::F::ONE);
    }
}
