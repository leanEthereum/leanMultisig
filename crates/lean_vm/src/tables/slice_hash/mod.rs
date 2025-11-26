use std::array;

use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::{ToUsize, get_poseidon_16_of_zero, poseidon16_permute, to_big_endian_in_field};

// "committed" columns
const COL_FLAG: ColIndex = 0;
const COL_INDEX_SEED: ColIndex = 1; // vectorized pointer
const COL_INDEX_INPUT: ColIndex = 2; // vectorized pointer
const COL_INDEX_OUTPUT: ColIndex = 3; // vectorized pointer
const COL_LEN: ColIndex = 4; // by multiple of 16

const INITIAL_COLS_DATA_LEFT: ColIndex = 6; // 16 columns for data left
const INITIAL_COLS_DATA_RIGHT: ColIndex = INITIAL_COLS_DATA_LEFT + 16; // 8 columns for data right
const INITIAL_COLS_DATA_RES: ColIndex = INITIAL_COLS_DATA_RIGHT + 8;

// "virtual" columns (vectorized lookups into memory)
const COLS_INDEX_LEFT: ColIndex = INITIAL_COLS_DATA_RES + 8;
const COLS_ROOT_START: ColIndex = COLS_LEAF_START + VECTOR_LEN;

const TOTAL_N_COLS: usize = COLS_ROOT_START + VECTOR_LEN;

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
        (0..COLS_LEAF_START).collect()
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
                index: COL_INDEX_LEAF,
                values: array::from_fn(|i| COLS_LEAF_START + i),
            },
            VectorLookupIntoMemory {
                index: COL_INDEX_ROOT,
                values: array::from_fn(|i| COLS_ROOT_START + i),
            },
        ]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: COL_FLAG,
            data: vec![
                COL_INDEX_LEAF,
                COL_LEAF_POSITION,
                COL_INDEX_ROOT,
                COL_HEIGHT,
            ],
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        let default_root = get_poseidon_16_of_zero()[..VECTOR_LEN].to_vec();
        [
            vec![
                F::ONE,                                   // flag
                F::ZERO,                                  // index_leaf
                F::ZERO,                                  // leaf_position
                F::from_usize(POSEIDON_16_NULL_HASH_PTR), // index_root
                F::ONE,
                F::ZERO, // is_left
            ],
            vec![F::ZERO; VECTOR_LEN], // data_left
            vec![F::ZERO; VECTOR_LEN], // data_right
            default_root.clone(),      // data_res
            vec![F::ZERO; VECTOR_LEN], // leaf
            default_root,              // root
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(
        &self,
        index_leaf: F,
        leaf_position: F,
        index_root: F,
        height: usize,
        ctx: &mut InstructionContext<'_>,
    ) -> Result<(), RunnerError> {
        let trace = &mut ctx.traces[self.identifier().index()].base;
        // TODO add row to poseidon16 trace

        let leaf_position = leaf_position.to_usize();
        assert!(height > 0);
        assert!(leaf_position < (1 << height));

        let auth_path = ctx.path_hints.pop_front().unwrap();
        assert_eq!(auth_path.len(), height);
        let mut leaf_position_bools = to_big_endian_in_field::<F>(!leaf_position, height);
        leaf_position_bools.reverse(); // little-endian

        let leaf = ctx.memory.get_vector(index_leaf.to_usize())?;

        trace[COL_FLAG].extend([vec![F::ONE], vec![F::ZERO; height - 1]].concat());
        trace[COL_INDEX_LEAF].extend(vec![index_leaf; height]);
        trace[COL_LEAF_POSITION].extend((0..height).map(|d| F::from_usize(leaf_position >> d)));
        trace[COL_INDEX_ROOT].extend(vec![index_root; height]);
        trace[COL_HEIGHT].extend((1..=height).rev().map(F::from_usize));
        trace[COL_IS_LEFT].extend(leaf_position_bools);

        let mut current_hash = leaf;
        for (d, neightbour) in auth_path.iter().enumerate() {
            let is_left = (leaf_position >> d) & 1 == 0;

            // TODO precompute (in parallel + SIMD) poseidons

            let (data_left, data_right) = if is_left {
                (current_hash, *neightbour)
            } else {
                (*neightbour, current_hash)
            };
            for i in 0..VECTOR_LEN {
                trace[INITIAL_COLS_DATA_LEFT + i].push(data_left[i]);
                trace[INITIAL_COLS_DATA_RIGHT + i].push(data_right[i]);
            }

            let mut input = [F::ZERO; VECTOR_LEN * 2];
            input[..VECTOR_LEN].copy_from_slice(&data_left);
            input[VECTOR_LEN..].copy_from_slice(&data_right);

            let output = match ctx.poseidon16_precomputed.get(*ctx.n_poseidon16_precomputed_used) {
                Some(precomputed) if precomputed.0 == input => {
                    *ctx.n_poseidon16_precomputed_used += 1;
                    precomputed.1
                }
                _ => poseidon16_permute(input),
            };

            current_hash = output[..VECTOR_LEN].try_into().unwrap();
            for i in 0..VECTOR_LEN {
                trace[INITIAL_COLS_DATA_RES + i].push(current_hash[i]);
            }
        }
        let root = current_hash;
        ctx.memory.set_vector(index_root.to_usize(), root)?;

        for i in 0..VECTOR_LEN {
            trace[COLS_LEAF_START + i].extend(vec![leaf[i]; height]);
            trace[COLS_ROOT_START + i].extend(vec![root[i]; height]);
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
        (0..TOTAL_N_COLS - 3 * VECTOR_LEN).collect() // skip COLS_DATA, COLS_LEAF, COLS_ROOT
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        7 + 6 * VECTOR_LEN
    }
    fn eval<AB: p3_air::AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let flag = up[COL_FLAG].clone();
        let index_leaf = up[COL_INDEX_LEAF].clone();
        let leaf_position = up[COL_LEAF_POSITION].clone();
        let index_root = up[COL_INDEX_ROOT].clone();
        let height = up[COL_HEIGHT].clone();
        let is_left = up[COL_IS_LEFT].clone();
        let data_left: [_; VECTOR_LEN] = array::from_fn(|i| up[INITIAL_COLS_DATA_LEFT + i].clone());
        let data_right: [_; VECTOR_LEN] = array::from_fn(|i| up[INITIAL_COLS_DATA_RIGHT + i].clone());
        let data_res: [_; VECTOR_LEN] = array::from_fn(|i| up[INITIAL_COLS_DATA_RES + i].clone());
        let leaf: [_; VECTOR_LEN] = array::from_fn(|i| up[COLS_LEAF_START + i].clone());
        let root: [_; VECTOR_LEN] = array::from_fn(|i| up[COLS_ROOT_START + i].clone());

        let down = builder.down_f();
        let flag_down = down[0].clone();
        let index_leaf_down = down[1].clone();
        let leaf_position_down = down[2].clone();
        let index_root_down = down[3].clone();
        let height_down = down[4].clone();
        let is_left_down = down[5].clone();
        let data_left_down: [_; VECTOR_LEN] = array::from_fn(|i| down[6 + i].clone());
        let data_right_down: [_; VECTOR_LEN] = array::from_fn(|i| down[6 + VECTOR_LEN + i].clone());

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            index_leaf.clone(),
            leaf_position.clone(),
            index_root.clone(),
            height.clone(),
        ));

        // TODO double check constraints

        builder.assert_bool(flag.clone());
        builder.assert_bool(is_left.clone());

        let not_flag_down = AB::F::ONE - flag_down.clone();
        let is_right = AB::F::ONE - is_left.clone();
        let is_right_down = AB::F::ONE - is_left_down.clone();

        // Parameters should not change as long as the flag has not been switched back to 1:
        builder.assert_zero(not_flag_down.clone() * (index_leaf_down.clone() - index_leaf.clone()));
        builder.assert_zero(not_flag_down.clone() * (index_root_down.clone() - index_root.clone()));

        // decrease height by 1 each step
        builder.assert_zero(not_flag_down.clone() * (height_down.clone() + AB::F::ONE - height.clone()));

        builder.assert_zero(
            not_flag_down.clone()
                * ((leaf_position_down.clone() * AB::F::TWO + is_right.clone()) - leaf_position.clone()),
        );

        // start (bottom of the tree)
        let starts_and_is_left = flag.clone() * is_left.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(starts_and_is_left.clone() * (data_left[i].clone() - leaf[i].clone()));
        }
        let starts_and_is_right = flag.clone() * is_right.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(starts_and_is_right.clone() * (data_right[i].clone() - leaf[i].clone()));
        }

        // transition (interior nodes)
        let transition_left = not_flag_down.clone() * is_left_down.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(transition_left.clone() * (data_left_down[i].clone() - data_res[i].clone()));
        }
        let transition_right = not_flag_down.clone() * is_right_down.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(transition_right.clone() * (data_right_down[i].clone() - data_res[i].clone()));
        }

        // end (top of the tree)
        builder.assert_zero(flag_down.clone() * leaf_position.clone() * (AB::F::ONE - leaf_position.clone())); // at last step, leaf position should be boolean
        let ends_and_is_left = flag_down.clone() * is_left.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(ends_and_is_left.clone() * (data_res[i].clone() - root[i].clone()));
        }
        let ends_and_is_right = flag_down.clone() * is_right.clone();
        for i in 0..VECTOR_LEN {
            builder.assert_zero(ends_and_is_right.clone() * (data_res[i].clone() - root[i].clone()));
        }
    }
}
