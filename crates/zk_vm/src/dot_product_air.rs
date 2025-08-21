use std::{borrow::Borrow, ops::Range};

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use vm::EF;

use crate::execution_trace::WitnessDotProduct;

/*
| StartFlag | Len | IndexA | IndexB | IndexRes | ValueA | ValueB | Res           | Computation                   |
| --------- | --- | ------ | ------ | -------- | ------ | ------ | ------------- | ----------------------------- |
| 1         | 4   | 90     | 211    | 74       | m[90]  | m[211] | m[74] = r3    | r3 = m[90] x m[211] + r2      |
| 0         | 3   | 91     | 212    | 74       | m[90]  | m[212] | m[74]         | r2 = m[91] x m[212] + r1      |
| 0         | 2   | 92     | 213    | 74       | m[90]  | m[213] | m[74]         | r1 = m[92] x m[213] + r0      |
| 0         | 1   | 93     | 214    | 74       | m[90]  | m[214] | m[74]         | r0 = m[93] x m[214]           |
| 1         | 10  | 1008   | 854    | 325      | m[90]  | m[854] | m[325] = r10' | r10' = m[1008] x m[854] + r9' |
| 0         | 9   | 1009   | 855    | 325      | m[90]  | m[855] | m[325]        | r9' = m[1009] x m[855] + r8'  |
| 0         | 8   | 1010   | 856    | 325      | m[90]  | m[856] | m[325]        | r8' = m[1010] x m[856] + r7'  |
| 0         | 7   | 1011   | 857    | 325      | m[90]  | m[857] | m[325]        | r7' = m[1011] x m[857] + r6'  |
| ...       | ... | ...    | ...    | ...      | ...    | ...    | ...           | ...                           |
*/

const DOT_PRODUCT_AIR_COLUMNS: usize = 9;
pub const DOT_PRODUCT_AIR_COLUMN_GROUPS: [Range<usize>; 5] = [0..1, 1..2, 2..5, 5..8, 8..9];

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
            flag_up,
            len_up,
            index_a_up,
            index_b_up,
            _index_res_up,
            value_a_up,
            value_b_up,
            res_up,
            computation_up,
        ] = up
            .iter()
            .map(|v| v.clone().into())
            .collect::<Vec<AB::Expr>>()
            .try_into()
            .unwrap();
        let [
            flag_down,
            len_down,
            index_a_down,
            index_b_down,
            _index_res_down,
            _value_a_down,
            _value_b_down,
            _res_down,
            computation_down,
        ] = down
            .iter()
            .map(|v| v.clone().into())
            .collect::<Vec<AB::Expr>>()
            .try_into()
            .unwrap();

        builder.assert_bool(flag_down.clone());

        let product_up = value_a_up * value_b_up;
        let not_flag_down = AB::Expr::ONE - flag_down.clone();
        builder.assert_eq(
            computation_up.clone(),
            flag_down.clone() * product_up.clone()
                + not_flag_down.clone() * (product_up + computation_down),
        );
        builder.assert_zero(
            not_flag_down.clone() * (len_up.clone() - (len_down + AB::Expr::ONE)),
        );
        builder.assert_zero(flag_down * (len_up - AB::Expr::ONE));
        builder.assert_zero(
            not_flag_down.clone() * (index_a_up - (index_a_down - AB::Expr::ONE)),
        );
        builder.assert_zero(
            not_flag_down * (index_b_up - (index_b_down - AB::Expr::ONE)),
        );

        builder.assert_zero(flag_up * (computation_up - res_up));
    }
}

pub fn build_dot_product_columns(witness: &[WitnessDotProduct]) -> (Vec<Vec<EF>>, usize) {
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

        flag.push(EF::ONE);
        flag.extend(EF::zero_vec(dot_product.len - 1));
        len.extend(((1..=dot_product.len).rev()).map(EF::from_usize));
        index_a.extend(
            (dot_product.addr_0..(dot_product.addr_0 + dot_product.len)).map(EF::from_usize),
        );
        index_b.extend(
            (dot_product.addr_1..(dot_product.addr_1 + dot_product.len)).map(EF::from_usize),
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
    )
}
