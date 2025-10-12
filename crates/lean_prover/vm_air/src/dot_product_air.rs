use lean_vm::{DIMENSION, EF, F, VECTOR_LEN, WitnessDotProduct};
use multilinear_toolkit::prelude::EFPacking;
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{BasedVectorSpace, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use std::{any::TypeId, borrow::Borrow};
use utils::ToUsize;
/*
(DIMENSION = 5)


| 0. StartFlag | 1. Len | 2. IndexA | 3. IndexB | 4. IndexRes |   |0. ValueA     | 1. ValueB   | 2. Res             | 3. Computation                           |
| ------------ | ------ | --------- | --------- | ----------- |   |------------- | ----------- | ------------------ | ---------------------------------------- |
| 1            | 4      | 90        | 211       | 74          |   |m[90..95]     | m[211..216] | m[74..79] = r3     | r3 = m[90..95] x m[211..216] + r2        |
| 0            | 3      | 95        | 216       | 74          |   | m[95..100]    | m[216..221] | m[74..79]          | r2 = m[95..100] x m[216..221] + r1       |
| 0            | 2      | 100       | 221       | 74          |   | m[100..105]   | m[221..226] | m[74..79]          | r1 = m[100..105] x m[221..226] + r0      |
| 0            | 1      | 105       | 226       | 74          |   | m[105..110]   | m[226..231] | m[74..79]          | r0 = m[105..110] x m[226..231]           |
| 1            | 10     | 1008      | 859       | 325         |   | m[1008..1013] | m[859..864] | m[325..330] = r10' | r10' = m[1008..1013] x m[859..864] + r9' |
| 0            | 9      | 1013      | 864       | 325         |   | m[1013..1018] | m[864..869] | m[325..330]        | r9' = m[1013..1018] x m[864..869] + r8'  |
| 0            | 8      | 1018      | 869       | 325         |   | m[1018..1023] | m[869..874] | m[325..330]        | r8' = m[1018..1023] x m[869..874] + r7'  |
| 0            | 7      | 1023      | 874       | 325         |   | m[1023..1028] | m[874..879] | m[325..330]        | r7' = m[1023..1028] x m[874..879] + r6'  |
| ...          | ...    | ...       | ...       | ...         |   | ...           | ...         | ...                | ...                                      |


# 5..24: IndexA:
- 9. IndexVec_A_1
- 10. IndexVec_A_2 (Virtual, = IndexVec_A_1 + 1)
- 11. OffsetVec_A (between 0 and 7)
- 12..20. ValueVec_A_1 (8 virtual colums)
- 20..28. ValueVec_A_2 (8 virtual colums)

constraints:

IndexVec_A_2 = IndexVec_A_1 + 1 (can probably be removed because it's implied by how we eval IndexVec_A_2)
OffsetVec_A . (1 - OffsetVec_A) . (2 - OffsetVec_A) . ... . (7 - OffsetVec_A) = 0
IndexA = 8.IndexVec_A_1 + OffsetVec_A
ValueA =
    413035751.(OffsetVec_A - 1).(OffsetVec_A - 2)...(OffsetVec_A - 7) . (ValueVec_A_1[0] + b1.ValueVec_A_1[1] + b2.ValueVec_A_1[2] + b3.ValueVec_A_1[3] + b4.ValueVec_A_1[4])
    1370162609.OffsetVec_A.(OffsetVec_A - 2)...(OffsetVec_A - 7) . (ValueVec_A_1[1] + b1.ValueVec_A_1[2] + b2.ValueVec_A_1[3] + b3.ValueVec_A_1[4] + b4.ValueVec_A_1[5])
    +
    ...
    +
    1717670682.OffsetVec_A.(OffsetVec_A - 1)...(OffsetVec_A - 6) . (ValueVec_A_1[7] + b1.ValueVec_A_2[0] + b2.ValueVec_A_2[1] + b3.ValueVec_A_2[2] + b4.ValueVec_A_2[3])


# 24..43: IndexB

// same

# 43..62: IndexRes

// same

#[test]
fn test() {
    use lean_vm::F;
    for i in 0..8 {
        let mut res = F::ONE;
        for j in 0..8 {
            if j != i {
                res = res * (F::from_usize(i) - F::from_usize(j));
            }
        }
        let _ = dbg!(F::ONE / res);
    }
}
*/

pub const DOT_PRODUCT_COL_START_FLAG: usize = 0;
pub const DOT_PRODUCT_COL_LEN: usize = 1;
pub const DOT_PRODUCT_COL_INDEX_A: usize = 2;
pub const DOT_PRODUCT_COL_INDEX_B: usize = 3;
pub const DOT_PRODUCT_COL_INDEX_RES: usize = 4;

pub const DOT_PRODUCT_COL_A_JUSTIFICATION_START: usize = 5;
pub const DOT_PRODUCT_COL_B_JUSTIFICATION_START: usize = 24;
pub const DOT_PRODUCT_COL_RES_JUSTIFICATION_START: usize = 43;

// the following apply to A, B, and Res
pub const DOT_PRODUCT_SUBCOL_INDEX_VEC_1: usize = 0;
pub const DOT_PRODUCT_SUBCOL_INDEX_VEC_2: usize = 1; // (virtual)
pub const DOT_PRODUCT_SUBCOL_OFFSET: usize = 2;
pub const DOT_PRODUCT_SUBCOL_VALUE_VEC_1_START: usize = 3; // 8 columns (virtual)
pub const DOT_PRODUCT_SUBCOL_VALUE_VEC_2_START: usize = 11; // 8 columns (virtual)

pub const DOT_PRODUCT_AIR_N_COLUMNS_F: usize = 5 + 19 * 3;
pub const DOT_PRODUCT_AIR_N_COLUMNS_EF: usize = 4;

pub const DOT_PRODUCT_EF_COL_VALUE_A: usize = 0;
pub const DOT_PRODUCT_EF_COL_VALUE_B: usize = 1;
pub const DOT_PRODUCT_EF_COL_RES: usize = 2;
pub const DOT_PRODUCT_EF_COL_COMPUTATION: usize = 3;

#[derive(Debug)]
pub struct DotProductAir;

impl<F> BaseAir<F> for DotProductAir {
    fn width_f(&self) -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_F
    }
    fn width_ef(&self) -> usize {
        DOT_PRODUCT_AIR_N_COLUMNS_EF
    }
    fn structured(&self) -> bool {
        true
    }
    fn degree(&self) -> usize {
        VECTOR_LEN
    }
}

impl<AB: AirBuilder> Air<AB> for DotProductAir
where
    AB::Var2: 'static,
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let (main_f, main_ef) = builder.main();
        let up_f = main_f.row_slice(0).unwrap();
        let up_f: &[AB::Var] = (*up_f).borrow();
        assert_eq!(up_f.len(), DOT_PRODUCT_AIR_N_COLUMNS_F);
        let down_f = main_f.row_slice(1).unwrap();
        let down_f: &[AB::Var] = (*down_f).borrow();
        assert_eq!(down_f.len(), DOT_PRODUCT_AIR_N_COLUMNS_F);
        let up_ef = main_ef.row_slice(0).unwrap();
        let up_ef: &[AB::Var2] = (*up_ef).borrow();
        assert_eq!(up_ef.len(), DOT_PRODUCT_AIR_N_COLUMNS_EF);
        let down_ef = main_ef.row_slice(1).unwrap();
        let down_ef: &[AB::Var2] = (*down_ef).borrow();
        assert_eq!(down_ef.len(), DOT_PRODUCT_AIR_N_COLUMNS_EF);

        let start_flag_up = up_f[DOT_PRODUCT_COL_START_FLAG].clone();
        let start_flag_down = down_f[DOT_PRODUCT_COL_START_FLAG].clone();
        let len_up = up_f[DOT_PRODUCT_COL_LEN].clone();
        let len_down = down_f[DOT_PRODUCT_COL_LEN].clone();
        let index_a_up = up_f[DOT_PRODUCT_COL_INDEX_A].clone();
        let index_a_down = down_f[DOT_PRODUCT_COL_INDEX_A].clone();
        let index_b_up = up_f[DOT_PRODUCT_COL_INDEX_B].clone();
        let index_b_down = down_f[DOT_PRODUCT_COL_INDEX_B].clone();
        let index_res_up = up_f[DOT_PRODUCT_COL_INDEX_RES].clone();
        let value_a_up = up_ef[DOT_PRODUCT_EF_COL_VALUE_A].clone();
        let value_b_up = up_ef[DOT_PRODUCT_EF_COL_VALUE_B].clone();
        let res_up = up_ef[DOT_PRODUCT_EF_COL_RES].clone();
        let computation_up = up_ef[DOT_PRODUCT_EF_COL_COMPUTATION].clone();
        let computation_down = down_ef[DOT_PRODUCT_EF_COL_COMPUTATION].clone();

        // TODO we could some some of the following computation in the base field

        builder.assert_bool(start_flag_down.clone());

        let product_up = value_a_up.clone() * value_b_up.clone();
        let not_flag_down = AB::Expr::ONE - start_flag_down.clone();
        builder.assert_eq_2(
            computation_up.clone(),
            product_up.clone() * start_flag_down.clone()
                + (product_up + computation_down) * not_flag_down.clone(),
        );
        builder.assert_zero(not_flag_down.clone() * (len_up.clone() - (len_down + AB::Expr::ONE)));
        builder.assert_zero(start_flag_down * (len_up - AB::Expr::ONE));
        builder.assert_zero(
            not_flag_down.clone()
                * (index_a_up.clone() - (index_a_down - AB::Expr::from_usize(DIMENSION))),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up.clone() - (index_b_down - AB::Expr::from_usize(DIMENSION))),
        );

        builder.assert_zero_2((computation_up - res_up.clone()) * start_flag_up);

        // Justification of the 3 values:
        for (index_ef, value_ef, justification_col_start) in [
            (
                index_a_up,
                value_a_up,
                DOT_PRODUCT_COL_A_JUSTIFICATION_START,
            ),
            (
                index_b_up,
                value_b_up,
                DOT_PRODUCT_COL_B_JUSTIFICATION_START,
            ),
            (
                index_res_up,
                res_up,
                DOT_PRODUCT_COL_RES_JUSTIFICATION_START,
            ),
        ] {
            builder.assert_zero(
                up_f[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_2].clone()
                    - (up_f[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_1].clone()
                        + AB::F::ONE),
            );
            let offset = up_f[justification_col_start + DOT_PRODUCT_SUBCOL_OFFSET].clone();
            builder.assert_zero(
                (0..VECTOR_LEN)
                    .map(|i| offset.clone() - AB::F::from_usize(i))
                    .product::<AB::Expr>(),
            );
            builder.assert_eq(
                index_ef,
                up_f[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_1].clone()
                    * AB::F::from_usize(VECTOR_LEN)
                    + offset.clone(),
            );

            const LAGRANGE_MULTIPLICATORS: [usize; VECTOR_LEN] = [
                413035751, 1370162609, 150925039, 458693746, 1672012687, 1979781394, 760543824,
                1717670682,
            ];

            let expected_value = (0..VECTOR_LEN)
                .map(|i| {
                    (0..DIMENSION)
                        .map(|k| {
                            // TODO multiplication by some basis element (in the sense of vector space) can be performed more efficiently
                            let basis = unsafe {
                                if TypeId::of::<AB::Var2>() == TypeId::of::<EF>() {
                                    std::mem::transmute_copy::<_, AB::Var2>(
                                        &<EF as BasedVectorSpace<F>>::ith_basis_element(k).unwrap(),
                                    )
                                } else {
                                    assert_eq!(
                                        TypeId::of::<AB::Var2>(),
                                        TypeId::of::<EFPacking<EF>>()
                                    );
                                    std::mem::transmute_copy::<_, AB::Var2>(&EFPacking::<EF>::from(
                                        <EF as BasedVectorSpace<F>>::ith_basis_element(k).unwrap(),
                                    ))
                                }
                            };
                            let factor = if i + k < VECTOR_LEN {
                                up_f[justification_col_start
                                    + DOT_PRODUCT_SUBCOL_VALUE_VEC_1_START
                                    + i
                                    + k]
                                    .clone()
                            } else {
                                up_f[justification_col_start
                                    + DOT_PRODUCT_SUBCOL_VALUE_VEC_2_START
                                    + i
                                    + k
                                    - VECTOR_LEN]
                                    .clone()
                            };
                            basis * factor
                        })
                        .sum::<AB::Var2>()
                        * ((0..VECTOR_LEN)
                            .filter(|j| *j != i)
                            .map(|j| offset.clone() - AB::F::from_usize(j))
                            .product::<AB::Expr>()
                            * AB::F::from_usize(LAGRANGE_MULTIPLICATORS[i]))
                })
                .sum::<AB::Var2>();
            builder.assert_eq_2(expected_value, value_ef);
        }
    }
}

pub fn build_dot_product_columns(
    witness: &[WitnessDotProduct],
    memory: &[F],
) -> (Vec<Vec<F>>, Vec<Vec<EF>>, usize) {
    let (
        mut flag,
        mut len,
        mut index_a,
        mut index_b,
        mut index_res,
        mut value_a,
        mut value_b,
        mut res,
        mut computation,
    ) = (
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    );
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

        flag.push(F::ONE);
        flag.extend(F::zero_vec(dot_product.len - 1));
        len.extend(((1..=dot_product.len).rev()).map(F::from_usize));
        index_a.extend(
            (0..dot_product.len).map(|i| F::from_usize(dot_product.addr_a + i * DIMENSION)),
        );
        index_b.extend(
            (0..dot_product.len).map(|i| F::from_usize(dot_product.addr_b + i * DIMENSION)),
        );
        index_res.extend(vec![F::from_usize(dot_product.addr_res); dot_product.len]);
        value_a.extend(dot_product.slice_0.clone());
        value_b.extend(dot_product.slice_1.clone());
        res.extend(vec![dot_product.res; dot_product.len]);
    }

    let padding_len = flag.len().next_power_of_two() - flag.len();
    flag.extend(vec![F::ONE; padding_len]);
    len.extend(vec![F::ONE; padding_len]);
    index_a.extend(F::zero_vec(padding_len));
    index_b.extend(F::zero_vec(padding_len));
    index_res.extend(F::zero_vec(padding_len));
    value_a.extend(EF::zero_vec(padding_len));
    value_b.extend(EF::zero_vec(padding_len));
    res.extend(EF::zero_vec(padding_len));
    computation.extend(EF::zero_vec(padding_len));

    let f_slice_to_usize = |slice: &[F]| slice.iter().map(|x| x.to_usize()).collect::<Vec<_>>();

    let mem_cols_a = build_justification_columns(&f_slice_to_usize(&index_a), memory);
    let mem_cols_b = build_justification_columns(&f_slice_to_usize(&index_b), memory);
    let mem_cols_res = build_justification_columns(&f_slice_to_usize(&index_res), memory);

    (
        [
            vec![flag, len, index_a, index_b, index_res],
            mem_cols_a,
            mem_cols_b,
            mem_cols_res,
        ]
        .concat(),
        vec![value_a, value_b, res, computation],
        padding_len,
    )
}

fn build_justification_columns(indexes: &[usize], memory: &[F]) -> Vec<Vec<F>> {
    assert!(indexes.len().is_power_of_two());
    let n = indexes.len();
    let mut res = vec![F::zero_vec(n); 19];
    for (i, &index) in indexes.iter().enumerate() {
        let vec_index_1 = index / VECTOR_LEN;
        let vec_index_2 = vec_index_1 + 1;
        res[0][i] = F::from_usize(vec_index_1);
        res[1][i] = F::from_usize(vec_index_2);
        let offset = index % VECTOR_LEN;
        res[2][i] = F::from_usize(offset);
        for j in 0..VECTOR_LEN {
            res[3 + j][i] = F::from(memory[vec_index_1 * VECTOR_LEN + j]);
            res[VECTOR_LEN + 3 + j][i] = F::from(memory[vec_index_2 * VECTOR_LEN + j]);
        }
    }
    res
}
