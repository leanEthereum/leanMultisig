use lean_vm::{DIMENSION, EF, F, VECTOR_LEN, WitnessDotProduct};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::Algebra;
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use std::array;
use std::borrow::Borrow;
use std::ops::{Add, Mul, Sub};
use utils::ToUsize;
use utils::transpose_slice_to_basis_coefficients;
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


# 9..28: IndexA:
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


# 28..47: IndexB

// same

# 47..66: IndexRes

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
pub const DOT_PRODUCT_COL_VALUE_A_START: usize = 5; // 5 columns
pub const DOT_PRODUCT_COL_VALUE_B_START: usize = 10; // 5 columns
pub const DOT_PRODUCT_COL_RES_START: usize = 15; // 5 columns
pub const DOT_PRODUCT_COL_COMPUTATION_START: usize = 20; // 5 columns

pub const DOT_PRODUCT_COL_A_JUSTIFICATION_START: usize = 25;
pub const DOT_PRODUCT_COL_B_JUSTIFICATION_START: usize = 44;
pub const DOT_PRODUCT_COL_RES_JUSTIFICATION_START: usize = 63;

// the following apply to A, B, and Res
pub const DOT_PRODUCT_SUBCOL_INDEX_VEC_1: usize = 0;
pub const DOT_PRODUCT_SUBCOL_INDEX_VEC_2: usize = 1; // (virtual)
pub const DOT_PRODUCT_SUBCOL_OFFSET: usize = 2;
pub const DOT_PRODUCT_SUBCOL_VALUE_VEC_1_START: usize = 3; // 8 columns (virtual)
pub const DOT_PRODUCT_SUBCOL_VALUE_VEC_2_START: usize = 11; // 8 columns (virtual)

const DOT_PRODUCT_AIR_COLUMNS: usize = 25 + 19 * 3;

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
        VECTOR_LEN
    }
}

impl<AB: AirBuilder> Air<AB> for DotProductAir
where
    AB::Expr: 'static,
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let up = main.row_slice(0).unwrap();
        let up: &[AB::Var] = (*up).borrow();
        assert_eq!(up.len(), DOT_PRODUCT_AIR_COLUMNS);
        let down = main.row_slice(1).unwrap();
        let down: &[AB::Var] = (*down).borrow();
        assert_eq!(down.len(), DOT_PRODUCT_AIR_COLUMNS);

        let start_flag_up = up[DOT_PRODUCT_COL_START_FLAG].clone();
        let start_flag_down = down[DOT_PRODUCT_COL_START_FLAG].clone();
        let len_up = up[DOT_PRODUCT_COL_LEN].clone();
        let len_down = down[DOT_PRODUCT_COL_LEN].clone();
        let index_a_up = up[DOT_PRODUCT_COL_INDEX_A].clone();
        let index_a_down = down[DOT_PRODUCT_COL_INDEX_A].clone();
        let index_b_up = up[DOT_PRODUCT_COL_INDEX_B].clone();
        let index_b_down = down[DOT_PRODUCT_COL_INDEX_B].clone();
        let index_res_up = up[DOT_PRODUCT_COL_INDEX_RES].clone();

        let make_array = |slice: &[AB::Var]| -> [AB::Var; DIMENSION] {
            slice[..DIMENSION]
                .iter()
                .cloned()
                .collect::<Vec<_>>()
                .try_into()
                .ok()
                .unwrap()
        };

        let value_a_up: [AB::Var; DIMENSION] = make_array(&up[DOT_PRODUCT_COL_VALUE_A_START..]);
        let value_b_up: [AB::Var; DIMENSION] = make_array(&up[DOT_PRODUCT_COL_VALUE_B_START..]);
        let res_up: [AB::Var; DIMENSION] = make_array(&up[DOT_PRODUCT_COL_RES_START..]);
        let computation_up: [AB::Var; DIMENSION] =
            make_array(&up[DOT_PRODUCT_COL_COMPUTATION_START..]);
        let computation_down: [AB::Var; DIMENSION] =
            make_array(&down[DOT_PRODUCT_COL_COMPUTATION_START..]);

        builder.assert_bool(start_flag_down.clone());

        let product_up = mul_columns_in_the_extension_field::<AB::F, AB::Var, AB::Expr>(
            &value_a_up,
            &value_b_up,
        );
        let not_flag_down = AB::Expr::ONE - start_flag_down.clone();
        for i in 0..DIMENSION {
            builder.assert_eq(
                computation_up[i].clone(),
                start_flag_down.clone() * product_up[i].clone()
                    + not_flag_down.clone() * (product_up[i].clone() + computation_down[i].clone()),
            );
            builder.assert_zero(
                start_flag_up.clone() * (computation_up[i].clone() - res_up[i].clone()),
            );
        }

        builder.assert_zero(not_flag_down.clone() * (len_up.clone() - (len_down + AB::Expr::ONE)));
        builder.assert_zero(start_flag_down * (len_up - AB::Expr::ONE));
        builder.assert_zero(
            not_flag_down.clone()
                * (index_a_up.clone() - (index_a_down - AB::Expr::from_usize(DIMENSION))),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up.clone() - (index_b_down - AB::Expr::from_usize(DIMENSION))),
        );

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
                up[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_2].clone()
                    - (up[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_1].clone()
                        + AB::F::ONE),
            );
            let offset = up[justification_col_start + DOT_PRODUCT_SUBCOL_OFFSET].clone();
            builder.assert_zero(
                (0..VECTOR_LEN)
                    .map(|i| offset.clone() - AB::F::from_usize(i))
                    .product::<AB::Expr>(),
            );
            builder.assert_eq(
                index_ef,
                up[justification_col_start + DOT_PRODUCT_SUBCOL_INDEX_VEC_1].clone()
                    * AB::F::from_usize(VECTOR_LEN)
                    + offset.clone(),
            );

            const LAGRANGE_MULTIPLICATORS: [usize; VECTOR_LEN] = [
                413035751, 1370162609, 150925039, 458693746, 1672012687, 1979781394, 760543824,
                1717670682,
            ];

            let mut expected_value_ef: [AB::Expr; DIMENSION] = [AB::Expr::ZERO; DIMENSION];
            (0..VECTOR_LEN).for_each(|i| {
                let factor = (0..VECTOR_LEN)
                    .filter(|j| *j != i)
                    .map(|j| offset.clone() - AB::F::from_usize(j))
                    .product::<AB::Expr>()
                    * AB::F::from_usize(LAGRANGE_MULTIPLICATORS[i]);
                (0..DIMENSION).for_each(|k| {
                    expected_value_ef[k] += factor.clone()
                        * if i + k < VECTOR_LEN {
                            up[justification_col_start
                                + DOT_PRODUCT_SUBCOL_VALUE_VEC_1_START
                                + i
                                + k]
                                .clone()
                        } else {
                            up[justification_col_start
                                + DOT_PRODUCT_SUBCOL_VALUE_VEC_2_START
                                + i
                                + k
                                - VECTOR_LEN]
                                .clone()
                        };
                })
            });
            for k in 0..DIMENSION {
                builder.assert_eq(expected_value_ef[k].clone(), value_ef[k].clone());
            }
        }
    }
}

fn mul_columns_in_the_extension_field<F: PrimeCharacteristicRing, Var, Expr>(
    a: &[Var; 5],
    b: &[Var; 5],
) -> [Expr; 5]
where
    Var: Clone
        + Add<F, Output = Expr>
        + Add<Var, Output = Expr>
        + Add<Expr, Output = Expr>
        + Sub<F, Output = Expr>
        + Sub<Var, Output = Expr>
        + Sub<Expr, Output = Expr>
        + Mul<F, Output = Expr>
        + Mul<Var, Output = Expr>
        + Mul<Expr, Output = Expr>,
    Expr: Algebra<F> + Algebra<Var>,
{
    let mut res = array::from_fn(|_| Expr::ZERO);
    // Convert b to R type for computation
    let b_r: [Expr; 5] = [
        b[0].clone().into(),
        b[1].clone().into(),
        b[2].clone().into(),
        b[3].clone().into(),
        b[4].clone().into(),
    ];

    let b_0_minus_3 = b_r[0].clone() - b_r[3].clone();
    let b_1_minus_4 = b_r[1].clone() - b_r[4].clone();
    let b_4_minus_2 = b_r[4].clone() - b_r[2].clone();

    let dot_product = |a: &[Var; 5], b: &[Expr; 5]| -> Expr {
        (0..5)
            .map(|i| a[i].clone() * b[i].clone())
            .reduce(|acc, x| acc + x)
            .unwrap()
    };

    // Constant term = a0*b0 + a1*b4 + a2*b3 + a3*b2 + a4*b1 - a4*b4
    res[0] = dot_product(
        a,
        &[
            b_r[0].clone(),
            b_r[4].clone(),
            b_r[3].clone(),
            b_r[2].clone(),
            b_1_minus_4.clone(),
        ],
    );

    // Linear term = a0*b1 + a1*b0 + a2*b4 + a3*b3 + a4*b2
    res[1] = dot_product(
        a,
        &[
            b_r[1].clone(),
            b_r[0].clone(),
            b_r[4].clone(),
            b_r[3].clone(),
            b_r[2].clone(),
        ],
    );

    // Square term = a0*b2 + a1*b1 - a1*b4 + a2*b0 - a2*b3 + a3*b4 - a3*b2 + a4*b3 - a4*b1 + a4*b4
    res[2] = dot_product(
        a,
        &[
            b_r[2].clone(),
            b_1_minus_4.clone(),
            b_0_minus_3.clone(),
            b_4_minus_2.clone(),
            b_r[3].clone() - b_1_minus_4.clone(),
        ],
    );

    // Cubic term = a0*b3 + a1*b2 + a2*b1 - a2*b4 + a3*b0 - a3*b3 + a4*b4 - a4*b2
    res[3] = dot_product(
        a,
        &[
            b_r[3].clone(),
            b_r[2].clone(),
            b_1_minus_4.clone(),
            b_0_minus_3.clone(),
            b_4_minus_2.clone(),
        ],
    );

    // Quartic term = a0*b4 + a1*b3 + a2*b2 + a3*b1 - a3*b4 + a4*b0 - a4*b3
    res[4] = dot_product(
        a,
        &[
            b_r[4].clone(),
            b_r[3].clone(),
            b_r[2].clone(),
            b_1_minus_4.clone(),
            b_0_minus_3.clone(),
        ],
    );
    res
}

pub fn build_dot_product_columns(
    witness: &[WitnessDotProduct],
    memory: &[F],
) -> (Vec<Vec<F>>, usize) {
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

    let slice_to_usize = |slice: &[F]| slice.iter().map(|x| x.to_usize()).collect::<Vec<_>>();

    let mem_cols_a = build_justification_columns(&slice_to_usize(&index_a), memory);
    let mem_cols_b = build_justification_columns(&slice_to_usize(&index_b), memory);
    let mem_cols_res = build_justification_columns(&slice_to_usize(&index_res), memory);

    (
        [
            vec![flag, len, index_a, index_b, index_res],
            transpose_slice_to_basis_coefficients(&value_a),
            transpose_slice_to_basis_coefficients(&value_b),
            transpose_slice_to_basis_coefficients(&res),
            transpose_slice_to_basis_coefficients(&computation),
            mem_cols_a,
            mem_cols_b,
            mem_cols_res,
        ]
        .concat(),
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
