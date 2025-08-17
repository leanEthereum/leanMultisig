use std::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;

use crate::{
    constant::{DOT_PRODUCT_AIR_COLUMNS, EF},
    witness::dot_product::WitnessDotProduct,
};

/// Dot Product AIR
///
/// ## Trace Layout
///
/// Each dot product is computed recursively, row by row, from the last element to the first.
/// The `start_flag` column marks the beginning of a new dot product computation (the first row
/// in its sequence). The `len` column acts as a counter, decreasing with each step.
///
/// An example trace for two dot products might look like this:
///
/// | start_flag | len | addr_a | addr_b | addr_res | val_a  | val_b  | res    | computation   |
/// |:----------:|:---:|:------:|:------:|:--------:|:------:|:------:|:------:|:-------------:|
/// |      1     |  4  |   90   |  211   |    74    | m[90]  | m[211] | m[74]  | v_a*v_b + C_next |
/// |      0     |  3  |   91   |  212   |    74    | m[91]  | m[212] | m[74]  | v_a*v_b + C_next |
/// |      0     |  2  |   92   |  213   |    74    | m[92]  | m[213] | m[74]  | v_a*v_b + C_next |
/// |      0     |  1  |   93   |  214   |    74    | m[93]  | m[214] | m[74]  | v_a*v_b       |
/// |      1     | 10  |  1008  |  854   |   325    | m[1008]| m[854] | m[325] | v_a*v_b + C_next |
/// | ...        | ... |  ...   |  ...   |   ...    | ...    | ...    | ...    | ...           |

#[derive(Debug, Default)]
pub struct DotProductAir;

impl<F> BaseAir<F> for DotProductAir {
    fn width(&self) -> usize {
        DOT_PRODUCT_AIR_COLUMNS
    }
}

impl<AB: AirBuilder> Air<AB> for DotProductAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        // Get a view of the main execution trace.
        let main = builder.main();

        // Get the current row (`local`) and the next row (`next`) from the trace.
        let local = main.row_slice(0).unwrap();
        let local = local.borrow();

        let next = main.row_slice(1).unwrap();
        let next = next.borrow();

        // Destructure the local row into named variables for clarity.
        let [
            start_flag_local,
            len_local,
            addr_a_local,
            addr_b_local,
            _addr_res_local,
            val_a_local,
            val_b_local,
            res_local,
            computation_local,
        ]: [AB::Expr; DOT_PRODUCT_AIR_COLUMNS] = local
            .iter()
            .map(|v| v.clone().into())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // Destructure the next row into named variables.
        let [
            start_flag_next,
            len_next,
            addr_a_next,
            addr_b_next,
            _addr_res_next,
            _val_a_next,
            _val_b_next,
            _res_next,
            computation_next,
        ]: [AB::Expr; DOT_PRODUCT_AIR_COLUMNS] = next
            .iter()
            .map(|v| v.clone().into())
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        // TRANSITION CONSTRAINTS

        // This constraint ensures that the `start_flag` is always boolean.
        //
        // It's checked on the `next` row, as the last row of the trace will have a dummy next row.
        builder.assert_bool(start_flag_next.clone());

        // This is the core recursive constraint for the dot product.
        //
        // `computation_local` = `val_a * val_b` + `computation_next` (if continuing a product)
        //
        // If the next row starts a new dot product (`start_flag_next`=1), `computation_next` is ignored.
        let product_local = val_a_local * val_b_local;
        let not_start_flag_next = AB::Expr::ONE - start_flag_next.clone();
        builder.assert_eq(
            computation_local.clone(),
            start_flag_next.clone() * product_local.clone()
                + not_start_flag_next.clone() * (product_local + computation_next),
        );

        // When not starting a new product, the length must decrement by 1.
        // `(1 - start_flag_next) * (len_local - (len_next + 1)) = 0`
        builder.assert_zero(
            not_start_flag_next.clone() * (len_local.clone() - (len_next + AB::Expr::ONE)),
        );

        // If the remaining length is 1, the next row must start a new product (`start_flag_next` = 1).
        //
        // This is enforced by `(len_local - 1) * (1 - start_flag_next) = 0`.
        builder.assert_zero((len_local - AB::Expr::ONE) * (AB::Expr::ONE - start_flag_next));

        // When not starting a new product, address `a` must increment by 1.
        // `(1 - start_flag_next) * (addr_a_next - (addr_a_local + 1)) = 0`
        builder.assert_zero(
            not_start_flag_next.clone() * (addr_a_next - (addr_a_local + AB::Expr::ONE)),
        );

        // When not starting a new product, address `b` must increment by 1.
        // `(1 - start_flag_next) * (addr_b_next - (addr_b_local + 1)) = 0`
        builder.assert_zero(not_start_flag_next * (addr_b_next - (addr_b_local + AB::Expr::ONE)));

        // If this is the first row of a dot product (`start_flag_local` = 1), the accumulated
        // `computation_local` must equal the final result `res_local`.
        builder.assert_zero(start_flag_local * (computation_local - res_local));
    }
}

/// ## Build Dot Product Columns
///
/// This function constructs the execution trace (witness) for the Dot Product AIR.
/// It takes a high-level description of dot product operations and expands it into the
/// row-by-row format required by the AIR constraints.
///
/// ### Arguments
/// * `witness`: A slice of `WitnessDotProduct` structs, each describing one dot product.
///
/// ### Returns
/// A tuple containing:
/// * A vector of columns representing the complete, padded execution trace.
/// * The number of padding rows that were added.
pub fn build_dot_product_columns(witness: &[WitnessDotProduct]) -> (Vec<Vec<EF>>, usize) {
    // Initialize vectors for each column of the trace.
    //
    // These will be populated and returned.
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

    // Process each high-level dot product operation from the witness.
    for dot_product in witness {
        // A dot product must have at least one term.
        assert!(dot_product.len > 0, "Dot product length must be positive.");

        // Build the `computation` column
        //
        // This is the most complex column, representing the recursive accumulation.
        // We build it backwards, from the last term to the first.
        let mut current_computation = vec![EF::ZERO; dot_product.len];
        let last_idx = dot_product.len - 1;

        // Base case: The computation for the last term is just the product of the last elements.
        current_computation[last_idx] =
            dot_product.slice_0[last_idx] * dot_product.slice_1[last_idx];

        // Recursive step: Iterate backwards from the second-to-last term.
        for i in (0..last_idx).rev() {
            // The computation at step `i` is the product of elements at `i` plus the computation from step `i+1`.
            current_computation[i] =
                current_computation[i + 1] + dot_product.slice_0[i] * dot_product.slice_1[i];
        }
        // Add the fully computed trace for this dot product to the main computation column.
        computation.extend(current_computation);

        // Build the other columns for the current dot product

        // The `flag` column is:
        // - 1 for the first row and
        // - 0 for all subsequent rows of this operation.
        flag.push(EF::ONE);
        flag.extend(vec![EF::ZERO; dot_product.len - 1]);

        // The `len` column is a countdown from the total length to 1.
        len.extend((1..=dot_product.len).rev().map(EF::from_usize));

        // The `index_a` and `index_b` columns are the memory addresses, incrementing from the start.
        index_a.extend(
            (dot_product.addr_0.offset..(dot_product.addr_0.offset + dot_product.len))
                .map(EF::from_usize),
        );
        index_b.extend(
            (dot_product.addr_1.offset..(dot_product.addr_1.offset + dot_product.len))
                .map(EF::from_usize),
        );

        // The `index_res` column holds the constant result address, repeated for every row.
        index_res.extend(vec![
            EF::from_usize(dot_product.addr_res.offset);
            dot_product.len
        ]);

        // The `value_a` and `value_b` columns are direct copies of the input slices.
        value_a.extend_from_slice(&dot_product.slice_0);
        value_b.extend_from_slice(&dot_product.slice_1);

        // The `res` column holds the final dot product result, repeated for every row.
        res.extend(vec![dot_product.res; dot_product.len]);
    }

    // Pad the trace to a power-of-two length
    //
    // This is required for efficient polynomial commitment schemes (e.g., using FFTs).
    let padding_len = flag.len().next_power_of_two() - flag.len();

    // If there is padding, add it to the trace
    if padding_len > 0 {
        // Use `start_flag=1` and `len=1` for padding rows. This is a simple state that
        // trivially satisfies the transition constraints when the other values are zero.
        flag.extend(vec![EF::ONE; padding_len]);
        len.extend(vec![EF::ONE; padding_len]);
        // The rest of the padding values can be zero.
        index_a.extend(vec![EF::ZERO; padding_len]);
        index_b.extend(vec![EF::ZERO; padding_len]);
        index_res.extend(vec![EF::ZERO; padding_len]);
        value_a.extend(vec![EF::ZERO; padding_len]);
        value_b.extend(vec![EF::ZERO; padding_len]);
        res.extend(vec![EF::ZERO; padding_len]);
        computation.extend(vec![EF::ZERO; padding_len]);
    }

    // Return the completed columns and the amount of padding added.
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
