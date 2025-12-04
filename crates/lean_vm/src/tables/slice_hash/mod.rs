use std::array;

use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::{ToUsize, get_poseidon_24_of_zero, poseidon24_permute};

// Does not support len = 1 (minimum len is 2)

// "committed" columns
const COL_FLAG: ColIndex = 0;
const COL_INDEX_SEED: ColIndex = 1; // vectorized pointer
const COL_INDEX_START: ColIndex = 2; // vectorized pointer
const COL_INDEX_START_BIS: ColIndex = 3; // = COL_INDEX_START + 1
const COL_INDEX_RES: ColIndex = 4; // vectorized pointer
const COL_LEN: ColIndex = 5;

const COL_LOOKUP_MEM_INDEX_SEED_OR_RES: ColIndex = 6; // = COL_INDEX_START if flag = 1, otherwise = COL_INDEX_RES
const INITIAL_COLS_DATA_RIGHT: ColIndex = 7;
const INITIAL_COLS_DATA_RES: ColIndex = INITIAL_COLS_DATA_RIGHT + VECTOR_LEN;

// "virtual" columns (vectorized lookups into memory)
const COL_LOOKUP_MEM_VALUES_SEED_OR_RES: ColIndex = INITIAL_COLS_DATA_RES + VECTOR_LEN; // 8 columns
const COL_LOOKUP_MEM_VALUES_LEFT: ColIndex = COL_LOOKUP_MEM_VALUES_SEED_OR_RES + VECTOR_LEN; // 16 columns

const TOTAL_N_COLS: usize = COL_LOOKUP_MEM_VALUES_LEFT + 2 * VECTOR_LEN;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SliceHashPrecompile;

impl TableT for SliceHashPrecompile {
    fn name(&self) -> &'static str {
        "slice_hash"
    }

    fn identifier(&self) -> Table {
        Table::slice_hash()
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        (0..COL_LOOKUP_MEM_VALUES_SEED_OR_RES).collect()
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
                index: COL_LOOKUP_MEM_INDEX_SEED_OR_RES,
                values: array::from_fn(|i| COL_LOOKUP_MEM_VALUES_SEED_OR_RES + i),
            },
            VectorLookupIntoMemory {
                index: COL_INDEX_START,
                values: array::from_fn(|i| COL_LOOKUP_MEM_VALUES_LEFT + i),
            },
            VectorLookupIntoMemory {
                index: COL_INDEX_START_BIS,
                values: array::from_fn(|i| COL_LOOKUP_MEM_VALUES_LEFT + VECTOR_LEN + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![
            Bus {
                table: BusTable::Constant(self.identifier()),
                direction: BusDirection::Pull,
                selector: BusSelector::Column(COL_FLAG),
                data: vec![COL_INDEX_SEED, COL_INDEX_START, COL_INDEX_RES, COL_LEN],
            },
            Bus {
                table: BusTable::Constant(Table::poseidon24_core()),
                direction: BusDirection::Push,
                selector: BusSelector::ConstantOne,
                data: [
                    (COL_LOOKUP_MEM_VALUES_LEFT..COL_LOOKUP_MEM_VALUES_LEFT + 16).collect::<Vec<ColIndex>>(),
                    (INITIAL_COLS_DATA_RIGHT..INITIAL_COLS_DATA_RIGHT + 8).collect::<Vec<ColIndex>>(),
                    (INITIAL_COLS_DATA_RES..INITIAL_COLS_DATA_RES + 8).collect::<Vec<ColIndex>>(),
                ]
                .concat(),
            },
        ]
    }

    fn padding_row_f(&self) -> Vec<F> {
        let default_hash = get_poseidon_24_of_zero()[2 * VECTOR_LEN..].to_vec();
        [
            vec![
                F::ONE,                          // flag
                F::from_usize(ZERO_VEC_PTR),     // index seed
                F::from_usize(ZERO_VEC_PTR),     // index_start
                F::from_usize(ZERO_VEC_PTR + 1), // index_start_bis
                F::from_usize(ZERO_VEC_PTR),     // index_res
                F::ONE,                          // len
                F::from_usize(ZERO_VEC_PTR),     // COL_LOOKUP_MEM_INDEX_SEED_OR_RES
            ],
            vec![F::ZERO; VECTOR_LEN],     // INITIAL_COLS_DATA_RIGHT
            default_hash,                  // INITIAL_COLS_DATA_RES
            vec![F::ZERO; VECTOR_LEN],     // COL_LOOKUP_MEM_VALUES_SEED_OR_RES
            vec![F::ZERO; VECTOR_LEN * 2], // COL_LOOKUP_MEM_VALUES_LEFT
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(
        &self,
        index_seed: F,
        index_start: F,
        index_res: F,
        len: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(len >= 2);

        let seed = ctx.memory.get_vector(index_seed.to_usize())?;
        let mut cap = seed;
        for i in 0..len {
            let index = index_start.to_usize() + i * 2;

            let mut input = [F::ZERO; VECTOR_LEN * 3];
            input[..VECTOR_LEN].copy_from_slice(&ctx.memory.get_vector(index)?);
            input[VECTOR_LEN..VECTOR_LEN * 2].copy_from_slice(&ctx.memory.get_vector(index + 1)?);
            input[VECTOR_LEN * 2..].copy_from_slice(&cap);
            // let output: [F; VECTOR_LEN] = poseidon24_permute(input)[VECTOR_LEN * 2..].try_into().unwrap();

            let output = match ctx.poseidon24_precomputed.get(*ctx.n_poseidon24_precomputed_used) {
                Some(precomputed) if precomputed.0 == input => {
                    *ctx.n_poseidon24_precomputed_used += 1;
                    precomputed.1
                }
                _ => poseidon24_permute(input)[VECTOR_LEN * 2..].try_into().unwrap(),
            };

            let trace = &mut ctx.traces.get_mut(&self.identifier()).unwrap().base;

            for j in 0..VECTOR_LEN * 2 {
                trace[COL_LOOKUP_MEM_VALUES_LEFT + j].push(input[j]);
            }
            for j in 0..VECTOR_LEN {
                trace[INITIAL_COLS_DATA_RIGHT + j].push(cap[j]);
            }
            for j in 0..VECTOR_LEN {
                trace[INITIAL_COLS_DATA_RES + j].push(output[j]);
            }

            add_poseidon_24_core_row(ctx.traces, 1, input, output);

            cap = output;
        }
        let trace = &mut ctx.traces.get_mut(&self.identifier()).unwrap().base;

        let final_res = cap;
        ctx.memory.set_vector(index_res.to_usize(), final_res)?;

        trace[COL_FLAG].extend([vec![F::ONE], vec![F::ZERO; len - 1]].concat());
        trace[COL_INDEX_SEED].extend(vec![index_seed; len]);
        trace[COL_INDEX_START].extend((0..len).map(|i| index_start + F::from_usize(i * 2)));
        trace[COL_INDEX_START_BIS].extend((0..len).map(|i| index_start + F::from_usize(i * 2 + 1)));
        trace[COL_INDEX_RES].extend(vec![index_res; len]);
        trace[COL_LEN].extend((1..=len).rev().map(F::from_usize));
        trace[COL_LOOKUP_MEM_INDEX_SEED_OR_RES].extend([vec![index_seed], vec![index_res; len - 1]].concat());
        for i in 0..VECTOR_LEN {
            trace[COL_LOOKUP_MEM_VALUES_SEED_OR_RES + i].extend([vec![seed[i]], vec![final_res[i]; len - 1]].concat());
        }

        Ok(())
    }
}

impl Air for SliceHashPrecompile {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        TOTAL_N_COLS
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        3
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        (0..INITIAL_COLS_DATA_RES).collect()
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        8 + 5 * VECTOR_LEN
    }
    fn eval<AB: p3_air::AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let flag = up[COL_FLAG].clone();
        let index_seed = up[COL_INDEX_SEED].clone();
        let index_start = up[COL_INDEX_START].clone();
        let index_start_bis = up[COL_INDEX_START_BIS].clone();
        let index_res = up[COL_INDEX_RES].clone();
        let len = up[COL_LEN].clone();
        let lookup_index_seed_or_res = up[COL_LOOKUP_MEM_INDEX_SEED_OR_RES].clone();
        let data_right: [_; VECTOR_LEN] = array::from_fn(|i| up[INITIAL_COLS_DATA_RIGHT + i].clone());
        let data_res: [_; VECTOR_LEN] = array::from_fn(|i| up[INITIAL_COLS_DATA_RES + i].clone());
        let data_seed_or_res_lookup_values: [_; VECTOR_LEN] =
            array::from_fn(|i| up[COL_LOOKUP_MEM_VALUES_SEED_OR_RES + i].clone());

        let down = builder.down_f();
        let flag_down = down[0].clone();
        let index_seed_down = down[1].clone();
        let index_start_down = down[2].clone();
        let _index_start_bis_down = down[3].clone();
        let index_res_down = down[4].clone();
        let len_down = down[5].clone();
        let _lookup_index_seed_or_res_down = down[6].clone();
        let data_right_down: [_; VECTOR_LEN] = array::from_fn(|i| down[7 + i].clone());

        let mut core_bus_data = [AB::F::ZERO; 24 + 8];
        core_bus_data[0..16].clone_from_slice(&up[COL_LOOKUP_MEM_VALUES_LEFT..][..16]);
        core_bus_data[16..24].clone_from_slice(&up[INITIAL_COLS_DATA_RIGHT..][..8]);
        core_bus_data[24..32].clone_from_slice(&up[INITIAL_COLS_DATA_RES..][..8]);

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            &[index_seed.clone(), index_start.clone(), index_res.clone(), len.clone()],
        ));

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(Table::poseidon24_core().index()),
            AB::F::ONE,
            &core_bus_data,
        ));

        // TODO double check constraints

        builder.assert_bool(flag.clone());

        let not_flag = AB::F::ONE - flag.clone();
        let not_flag_down = AB::F::ONE - flag_down.clone();

        builder.assert_eq(
            lookup_index_seed_or_res.clone(),
            flag.clone() * index_seed.clone() + not_flag.clone() * index_res.clone(),
        );

        // index_start_bis = index_start + 1
        builder.assert_eq(index_start_bis.clone(), index_start.clone() + AB::F::ONE);

        // Parameters should not change as long as the flag has not been switched back to 1:
        builder.assert_zero(not_flag_down.clone() * (index_seed_down.clone() - index_seed.clone()));
        builder.assert_zero(not_flag_down.clone() * (index_res_down.clone() - index_res.clone()));

        builder.assert_zero(not_flag_down.clone() * (index_start_down.clone() - (index_start.clone() + AB::F::TWO)));

        // decrease len by 1 each step
        builder.assert_zero(not_flag_down.clone() * (len_down.clone() + AB::F::ONE - len.clone()));

        // start: ingest the seed
        for i in 0..VECTOR_LEN {
            builder.assert_zero(flag.clone() * (data_right[i].clone() - data_seed_or_res_lookup_values[i].clone()));
        }

        // transition
        for i in 0..VECTOR_LEN {
            builder.assert_zero(not_flag_down.clone() * (data_res[i].clone() - data_right_down[i].clone()));
        }

        // end
        builder.assert_zero(flag_down.clone() * (len.clone() - AB::F::ONE)); // at last step, len should be 1
        for i in 0..VECTOR_LEN {
            builder.assert_zero(
                not_flag.clone()
                    * flag_down.clone()
                    * (data_res[i].clone() - data_seed_or_res_lookup_values[i].clone()),
            );
        }
    }
}
