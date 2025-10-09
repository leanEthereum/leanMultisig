use std::{array, borrow::Borrow};

use lean_vm::{DIMENSION, EF, F, VECTOR_LEN, WitnessDotProduct};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use rayon::iter::{IntoParallelIterator, IntoParallelRefIterator, ParallelIterator};
use utils::{ToUsize, field_slice_as_base};
/*


(DIMENSION = 5)


| 0. StartFlag | 1. Len | 2. IndexA | 3. IndexB | 4. IndexRes | 5. ValueA     | 6. ValueB   | 7. Res             | 8. Computation                           |
| ------------ | ------ | --------- | --------- | ----------- | ------------- | ----------- | ------------------ | ---------------------------------------- |
| 1            | 4      | 90        | 211       | 74          | m[90..95]     | m[211..216] | m[74..79] = r3     | r3 = m[90..95] x m[211..216] + r2        |
| 0            | 3      | 95        | 216       | 74          | m[95..100]    | m[216..221] | m[74..79]          | r2 = m[95..100] x m[216..221] + r1       |
| 0            | 2      | 100       | 221       | 74          | m[100..105]   | m[221..226] | m[74..79]          | r1 = m[100..105] x m[221..226] + r0      |
| 0            | 1      | 105       | 226       | 74          | m[105..110]   | m[226..231] | m[74..79]          | r0 = m[105..110] x m[226..231]           |
| 1            | 10     | 1008      | 859       | 325         | m[1008..1013] | m[859..864] | m[325..330] = r10' | r10' = m[1008..1013] x m[859..864] + r9' |
| 0            | 9      | 1013      | 864       | 325         | m[1013..1018] | m[864..869] | m[325..330]        | r9' = m[1013..1018] x m[864..869] + r8'  |
| 0            | 8      | 1018      | 869       | 325         | m[1018..1023] | m[869..874] | m[325..330]        | r8' = m[1018..1023] x m[869..874] + r7'  |
| 0            | 7      | 1023      | 874       | 325         | m[1023..1028] | m[874..879] | m[325..330]        | r7' = m[1023..1028] x m[874..879] + r6'  |
| ...          | ...    | ...       | ...       | ...         | ...           | ...         | ...                | ...                                      |

*/

const DOT_PRODUCT_AIR_COLUMNS: usize = 9;

#[derive(Debug)]
pub struct DotProductAir;

impl<F> BaseAir<F> for DotProductAir {
    fn width(&self) -> usize {
        DOT_PRODUCT_AIR_COLUMNS
    }
    fn structured(&self) -> bool {
        true
    }
    fn degree(&self) -> usize {
        3
    }
}

impl<AB: AirBuilder> Air<AB> for DotProductAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main.row_slice(0).unwrap();
        let up: &[AB::Var] = (*up).borrow();
        assert_eq!(up.len(), DOT_PRODUCT_AIR_COLUMNS);
        let down = main.row_slice(1).unwrap();
        let down: &[AB::Var] = (*down).borrow();
        assert_eq!(down.len(), DOT_PRODUCT_AIR_COLUMNS);

        let [
            start_flag_up,
            len_up,
            index_a_up,
            index_b_up,
            _index_res_up,
            value_a_up,
            value_b_up,
            res_up,
            computation_up,
        ] = up.to_vec().try_into().ok().unwrap();
        let [
            start_flag_down,
            len_down,
            index_a_down,
            index_b_down,
            _index_res_down,
            _value_a_down,
            _value_b_down,
            _res_down,
            computation_down,
        ] = down.to_vec().try_into().ok().unwrap();

        // TODO we could some some of the following computation in the base field

        builder.assert_bool(start_flag_down.clone());

        let product_up = value_a_up * value_b_up;
        let not_flag_down = AB::Expr::ONE - start_flag_down.clone();
        builder.assert_eq(
            computation_up.clone(),
            start_flag_down.clone() * product_up.clone()
                + not_flag_down.clone() * (product_up + computation_down),
        );
        builder.assert_zero(not_flag_down.clone() * (len_up.clone() - (len_down + AB::Expr::ONE)));
        builder.assert_zero(start_flag_down * (len_up - AB::Expr::ONE));
        builder.assert_zero(
            not_flag_down.clone() * (index_a_up - (index_a_down - AB::Expr::from_usize(DIMENSION))),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up - (index_b_down - AB::Expr::from_usize(DIMENSION))),
        );

        builder.assert_zero(start_flag_up * (computation_up - res_up));
    }
}

pub fn build_dot_product_columns(
    witness: &[WitnessDotProduct],
    memory: &[F],
) -> (Vec<Vec<EF>>, usize, Vec<Vec<F>>, Vec<F>) {
    let mut flag = Vec::new();
    let mut len = Vec::new();
    let mut index_a = Vec::new();
    let mut index_b = Vec::new();
    let mut index_res = Vec::new();
    let mut value_a = Vec::new();
    let mut value_b = Vec::new();
    let mut res = Vec::new();
    let mut computation = Vec::new();

    for dot_product in witness {
        assert!(dot_product.len > 0);

        // computation
        {
            computation.extend(EF::zero_vec(dot_product.len));
            let new_size = computation.len();
            computation[new_size - 1] =
                dot_product.slice_0[dot_product.len - 1] * dot_product.slice_1[dot_product.len - 1];
            for i in 0..dot_product.len - 1 {
                computation[new_size - 2 - i] = computation[new_size - 1 - i]
                    + dot_product.slice_0[dot_product.len - 2 - i]
                        * dot_product.slice_1[dot_product.len - 2 - i];
            }
        }

        flag.push(EF::ONE);
        flag.extend(EF::zero_vec(dot_product.len - 1));
        len.extend(((1..=dot_product.len).rev()).map(EF::from_usize));
        index_a.extend(
            (0..dot_product.len).map(|i| EF::from_usize(dot_product.addr_0 + i * DIMENSION)),
        );
        index_b.extend(
            (0..dot_product.len).map(|i| EF::from_usize(dot_product.addr_1 + i * DIMENSION)),
        );
        index_res.extend(vec![EF::from_usize(dot_product.addr_res); dot_product.len]);
        value_a.extend(dot_product.slice_0.clone());
        value_b.extend(dot_product.slice_1.clone());
        res.extend(vec![dot_product.res; dot_product.len]);
    }

    let padding_len = flag.len().next_power_of_two() - flag.len();
    flag.extend(vec![EF::ONE; padding_len]);
    len.extend(vec![EF::ONE; padding_len]);
    index_a.extend(EF::zero_vec(padding_len));
    index_b.extend(EF::zero_vec(padding_len));
    index_res.extend(EF::zero_vec(padding_len));
    value_a.extend(EF::zero_vec(padding_len));
    value_b.extend(EF::zero_vec(padding_len));
    res.extend(EF::zero_vec(padding_len));
    computation.extend(EF::zero_vec(padding_len));

    let (memory_table, meta_indexes) =
        build_dot_product_memory_columns(&index_a, &index_b, &index_res, memory);

    (
        vec![
            flag,
            len,
            index_a,
            index_b,
            index_res,
            value_a,
            value_b,
            res,
            computation,
        ],
        padding_len,
        memory_table,
        meta_indexes,
    )
}

/*
DPMA = Dot Product Memory Air

The goal of this table is to pull lookups for ()

Columns:
- EFIndex (normal pointer to 5 base field elements)
- EFValue (corresponding value = 5 columns)
- VectorizedIndex
- VectorizedValue (virtual)
- Offset0
- Offset1
- ...
- Offset7

Constraints:
- Offset0, ..., Offset7 are boolean
- Offset0 + ... + Offset7 = 1
define Overlap = Offset4 + ... + Offset7
Overlap * (next(EFIndex) - (EFIndex + Offset7 + Offset6 * 2 + Offset5 * 3 + Offset4 * 4)) = 0
EFIndex = 8.VectorizedIndex + Offset0 + 2.Offset1 + 3.Offset2 + ... + 7.Offset7
- ValueA[0] = Offset0.VectorizedValue[0] + Offset1.VectorizedValue[1] + ... + Offset7.VectorizedValue[7]
- ValueA[1] = Offset0.VectorizedValue[1] + Offset1.VectorizedValue[2] + ... + Offset7.next(VectorizedValue)[0]
...
- ValueA[4] = Offset0.VectorizedValue[4] + Offset1.VectorizedValue[5] + ... + Offset7.next(VectorizedValue)[3]

*/

const DPMA_N_COLUMNS: usize = 23;

const DPMA_COL_EF_INDEX: usize = 0;
const DPMA_COL_EF_VALUE_START: usize = 1; // 5 columns
const DPMA_COL_VECTOR_INDEX: usize = 6;
const DPMA_COL_VECTOR_VALUE_START: usize = 7; // 8 columns
const DPMA_COL_OFFSET_START: usize = 15; // 8 columns

#[derive(Debug)]
pub struct DotProductMemoryAir;

impl<F> BaseAir<F> for DotProductMemoryAir {
    fn width(&self) -> usize {
        DPMA_N_COLUMNS
    }
    fn structured(&self) -> bool {
        true
    }
    fn degree(&self) -> usize {
        2
    }
}

impl<AB: AirBuilder> Air<AB> for DotProductMemoryAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let current = main.row_slice(0).unwrap();
        let current: &[AB::Var] = (*current).borrow();
        assert_eq!(current.len(), DPMA_N_COLUMNS);
        let next = main.row_slice(1).unwrap();
        let next: &[AB::Var] = (*next).borrow();
        assert_eq!(next.len(), DPMA_N_COLUMNS);

        let ef_index = current[DPMA_COL_EF_INDEX].clone().into();
        let ef_value: [AB::Expr; DIMENSION] =
            array::from_fn(|i| current[DPMA_COL_EF_VALUE_START + i].clone().into());
        let vector_index = current[DPMA_COL_VECTOR_INDEX].clone().into();
        let vector_value: [AB::Expr; VECTOR_LEN] =
            array::from_fn(|i| current[DPMA_COL_VECTOR_VALUE_START + i].clone().into());
        let offsets: [AB::Expr; VECTOR_LEN] =
            array::from_fn(|i| current[DPMA_COL_OFFSET_START + i].clone().into());

        let next_ef_index = next[DPMA_COL_EF_INDEX].clone().into();
        let next_vector_value: [AB::Expr; VECTOR_LEN] =
            array::from_fn(|i| next[DPMA_COL_VECTOR_VALUE_START + i].clone().into());

        // Constraint: Offset0, ..., Offset7 are boolean
        for offset in offsets.iter() {
            builder.assert_bool(offset.clone());
        }

        // Constraint: Offset0 + ... + Offset7 = 1
        builder.assert_one(offsets.iter().cloned().sum::<AB::Expr>());

        // Constraint: Overlap * (next(EFIndex) - (EFIndex + Offset7 + Offset6 * 2 + Offset5 * 3 + Offset4 * 4)) = 0
        // Overlap = Offset4 + ... + Offset7
        let overlap =
            offsets[4].clone() + offsets[5].clone() + offsets[6].clone() + offsets[7].clone();
        let increment = offsets[7].clone()
            + offsets[6].clone() * AB::F::TWO
            + offsets[5].clone() * AB::F::from_usize(3)
            + offsets[4].clone() * AB::F::from_usize(4);
        builder.assert_zero(overlap * (next_ef_index - (ef_index.clone() + increment)));

        // Constraint: EFIndex = 8.VectorizedIndex + Offset0 + 2.Offset1 + 3.Offset2 + ... + 7.Offset7
        let ef_index_from_vector = vector_index * AB::F::from_usize(8)
            + (1..VECTOR_LEN)
                .map(|i| offsets[i].clone() * AB::F::from_usize(i))
                .sum::<AB::Expr>();
        builder.assert_eq(ef_index, ef_index_from_vector);

        // Constraints: ValueA[i] = weighted sum of VectorizedValue elements
        for i in 0..DIMENSION {
            let mut value_constraint = AB::Expr::ZERO;
            for j in 0..8 {
                if i + j < 8 {
                    // Use current row's vector_value
                    value_constraint =
                        value_constraint + offsets[j].clone() * vector_value[i + j].clone();
                } else {
                    // Use next row's vector_value
                    value_constraint = value_constraint
                        + offsets[j].clone() * next_vector_value[i + j - 8].clone();
                }
            }
            builder.assert_eq(ef_value[i].clone(), value_constraint);
        }
    }
}

fn build_dot_product_memory_columns(
    index_a: &[EF],
    index_b: &[EF],
    index_res: &[EF],
    memory: &[F],
) -> (Vec<Vec<F>>, Vec<F>) {
    // the resulting table is padded (to the next power of two)
    let all_indexes = field_slice_as_base::<F, _>(&[index_a, index_b, index_res].concat()).unwrap();
    let mut all_indexes_sorted = all_indexes.clone();
    all_indexes_sorted.sort_unstable();
    all_indexes_sorted.dedup();
    let all_indexes_sorted = all_indexes_sorted
        .into_par_iter()
        .map(|f| f.to_usize())
        .collect::<Vec<_>>();

    let indexes_with_overlaps = (0..all_indexes_sorted.len())
        .flat_map(|i| {
            if all_indexes_sorted[i] % VECTOR_LEN > VECTOR_LEN - DIMENSION
                && (i == all_indexes_sorted.len() - 1
                    || all_indexes_sorted[i + 1] != all_indexes_sorted[i] + 1)
            {
                vec![all_indexes_sorted[i], 1 + all_indexes_sorted[i]]
            } else {
                vec![all_indexes_sorted[i]]
            }
        })
        .collect::<Vec<_>>();

    let len_padded = indexes_with_overlaps.len().next_power_of_two();
    let mut table = vec![vec![F::ZERO; len_padded]; DPMA_N_COLUMNS];

    for (i, &index) in indexes_with_overlaps.iter().enumerate() {
        let vec_index = index / VECTOR_LEN;
        let offset = index % VECTOR_LEN;

        table[DPMA_COL_EF_INDEX][i] = F::from_usize(index);
        for j in 0..DIMENSION {
            table[DPMA_COL_EF_VALUE_START + j][i] = memory[index + j];
        }
        table[DPMA_COL_VECTOR_INDEX][i] = F::from_usize(vec_index);
        for j in 0..VECTOR_LEN {
            table[DPMA_COL_VECTOR_VALUE_START + j][i] = memory[8 * vec_index + j];
        }
        table[DPMA_COL_OFFSET_START + offset][i] = F::ONE;
    }

    let ef_indexes_usize = table[0]
        .par_iter()
        .map(|f| f.to_usize())
        .collect::<Vec<_>>();

    let meta_indexes = all_indexes
        .par_iter()
        .map(|index_ef| {
            // we need to find i such that ef_indexes_usize[i] == index_ef
            F::from_usize(
                ef_indexes_usize
                    .binary_search(&index_ef.to_usize())
                    .unwrap(),
            )
        })
        .collect::<Vec<_>>();

    (table, meta_indexes)
}
