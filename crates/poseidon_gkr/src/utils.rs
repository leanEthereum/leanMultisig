use std::array;

use backend::*;
use tracing::instrument;

use crate::EF;
use crate::F;

#[instrument(skip_all)]
pub fn build_poseidon_inv_matrices<const WIDTH: usize>() -> ([[F; WIDTH]; WIDTH], [[F; WIDTH]; WIDTH])
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut external_matrix: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| F::ZERO));
    for (i, row) in external_matrix.iter_mut().enumerate() {
        row[i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(row);
    }
    external_matrix = transpose_matrix(&external_matrix);
    let inv_external_matrix = inverse_matrix(&external_matrix);

    let mut internal_matrix: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| F::ZERO));
    for (i, row) in internal_matrix.iter_mut().enumerate() {
        row[i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(row);
    }
    internal_matrix = transpose_matrix(&internal_matrix);
    let inv_internal_matrix = inverse_matrix(&internal_matrix);

    (inv_external_matrix, inv_internal_matrix)
}

pub fn apply_matrix<const WIDTH: usize>(matrix: &[[F; WIDTH]; WIDTH], claims: &[EF]) -> Vec<EF> {
    assert_eq!(claims.len(), WIDTH);
    let mut result = vec![EF::ZERO; WIDTH];
    for (i, row) in matrix.iter().enumerate() {
        for (j, &entry) in row.iter().enumerate() {
            result[i] += claims[j] * entry;
        }
    }
    result
}

fn transpose_matrix<const WIDTH: usize>(matrix: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH]; WIDTH] {
    let mut result: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| F::ZERO));
    for (i, row) in matrix.iter().enumerate() {
        for (j, &val) in row.iter().enumerate() {
            result[j][i] = val;
        }
    }
    result
}

fn inverse_matrix<const WIDTH: usize>(matrix: &[[F; WIDTH]; WIDTH]) -> [[F; WIDTH]; WIDTH] {
    // Gaussian elimination over F
    let mut augmented: [[F; WIDTH]; WIDTH] = *matrix;
    let mut inv: [[F; WIDTH]; WIDTH] = array::from_fn(|i| {
        let mut row = [F::ZERO; WIDTH];
        row[i] = F::ONE;
        row
    });

    for col in 0..WIDTH {
        // Find pivot
        let pivot = (col..WIDTH)
            .find(|&row| !augmented[row][col].is_zero())
            .expect("Matrix is singular");
        augmented.swap(col, pivot);
        inv.swap(col, pivot);

        let pivot_inv = augmented[col][col].inverse();
        for j in 0..WIDTH {
            augmented[col][j] *= pivot_inv;
            inv[col][j] *= pivot_inv;
        }

        for row in 0..WIDTH {
            if row == col {
                continue;
            }
            let factor = augmented[row][col];
            for j in 0..WIDTH {
                augmented[row][j] -= factor * augmented[col][j];
                inv[row][j] -= factor * inv[col][j];
            }
        }
    }
    inv
}
