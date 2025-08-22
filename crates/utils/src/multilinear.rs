use std::borrow::Borrow;

use p3_field::{ExtensionField, Field, dot_product};
use rayon::prelude::*;
use tracing::instrument;
use whir_p3::poly::evals::EvaluationsList;

use crate::{EFPacking, PF};

pub fn fold_multilinear_in_large_field<F: Field, EF: ExtensionField<F>>(
    m: &[F],
    scalars: &[EF],
) -> Vec<EF> {
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();
    (0..new_size)
        .into_par_iter()
        .map(|i| {
            scalars
                .iter()
                .enumerate()
                .map(|(j, s)| *s * m[i + j * new_size])
                .sum()
        })
        .collect()
}

pub fn fold_extension_packed<EF: ExtensionField<PF<EF>>>(
    m: &[EFPacking<EF>],
    scalars: &[EF],
) -> Vec<EFPacking<EF>> {
    assert!(scalars.len().is_power_of_two() && scalars.len() <= m.len());
    let new_size = m.len() / scalars.len();

    (0..new_size)
        .into_par_iter()
        .map(|i| {
            scalars
                .iter()
                .enumerate()
                .map(|(j, s)| m[i + j * new_size] * *s)
                .sum()
        })
        .collect()
}

#[instrument(name = "multilinears_linear_combination", skip_all)]
pub fn multilinears_linear_combination<
    F: Field,
    EF: ExtensionField<F>,
    P: Borrow<[F]> + Send + Sync,
>(
    pols: &[P],
    scalars: &[EF],
) -> Vec<EF> {
    assert_eq!(pols.len(), scalars.len());
    let n_vars = pols[0].borrow().num_variables();
    assert!(pols.iter().all(|p| p.borrow().num_variables() == n_vars));
    (0..1 << n_vars)
        .into_par_iter()
        .map(|i| dot_product(scalars.iter().copied(), pols.iter().map(|p| p.borrow()[i])))
        .collect::<Vec<_>>()
}

pub fn batch_fold_multilinear_in_large_field<F: Field, EF: ExtensionField<F>>(
    polys: &[&[F]],
    scalars: &[EF],
) -> Vec<Vec<EF>> {
    polys
        .par_iter()
        .map(|poly| fold_multilinear_in_large_field(poly, scalars))
        .collect()
}

pub fn batch_fold_multilinear_in_large_field_packed<EF: ExtensionField<PF<EF>>>(
    polys: &[&[EFPacking<EF>]],
    scalars: &[EF],
) -> Vec<Vec<EFPacking<EF>>> {
    polys
        .iter()
        .map(|poly| fold_extension_packed(poly, scalars))
        .collect()
}

#[instrument(name = "add_multilinears", skip_all)]
pub fn add_multilinears<F: Field>(pol1: &[F], pol2: &[F]) -> Vec<F> {
    assert_eq!(pol1.len(), pol2.len());
    let mut dst = pol1.to_vec();
    dst.par_iter_mut()
        .zip(pol2.par_iter())
        .for_each(|(a, b)| *a += *b);
    dst
}

pub fn padd_with_zero_to_next_power_of_two<F: Field>(pol: &[F]) -> Vec<F> {
    let next_power_of_two = pol.len().next_power_of_two();
    let mut padded = pol.to_vec();
    padded.resize(next_power_of_two, F::ZERO);
    padded
}
