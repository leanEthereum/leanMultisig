use std::array;

use multilinear_toolkit::prelude::*;
use p3_koala_bear::{GenericPoseidon2LinearLayersKoalaBear, KoalaBearInternalLayerParameters, KoalaBearParameters};
use p3_monty_31::InternalLayerBaseParameters;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use tracing::instrument;

use crate::F;

#[instrument(skip_all)]
pub fn build_poseidon_inv_matrices<const WIDTH: usize>() -> ([[F; WIDTH]; WIDTH], [[F; WIDTH]; WIDTH])
where
    KoalaBearInternalLayerParameters: InternalLayerBaseParameters<KoalaBearParameters, WIDTH>,
{
    let mut mds_matrix: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| F::ZERO));
    for (i, row) in mds_matrix.iter_mut().enumerate() {
        row[i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::external_linear_layer(row);
    }
    mds_matrix = transpose_matrix(&mds_matrix);
    let inv_mds_matrix = inverse_matrix(&mds_matrix);

    let mut light_matrix: [[F; WIDTH]; WIDTH] = array::from_fn(|_| array::from_fn(|_| F::ZERO));
    for (i, row) in light_matrix.iter_mut().enumerate() {
        row[i] = F::ONE;
        GenericPoseidon2LinearLayersKoalaBear::internal_linear_layer(row);
    }
    light_matrix = transpose_matrix(&light_matrix);
    let inv_light_matrix = inverse_matrix(&light_matrix);

    (inv_mds_matrix, inv_light_matrix)
}
