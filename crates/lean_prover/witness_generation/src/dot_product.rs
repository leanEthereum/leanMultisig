use lean_vm::{DIMENSION, EF, WitnessDotProduct};
use multilinear_toolkit::prelude::*;

pub fn build_dot_product_columns(
    witness: &[WitnessDotProduct],
    min_n_rows: usize,
) -> (Vec<Vec<EF>>, usize) {
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

    let padding_len = flag.len().next_power_of_two().max(min_n_rows) - flag.len();
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
