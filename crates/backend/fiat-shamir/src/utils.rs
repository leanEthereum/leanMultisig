use field::{BasedVectorSpace, ExtensionField, Field, PrimeCharacteristicRing, PrimeField64};
use symetric::Compression;

use crate::challenger::{Challenger, RATE, WIDTH};

pub(crate) type PF<F> = <F as PrimeCharacteristicRing>::PrimeSubfield;

pub fn flatten_scalars_to_base<F: Field, EF: ExtensionField<F>>(scalars: &[EF]) -> Vec<F> {
    scalars
        .iter()
        .flat_map(BasedVectorSpace::as_basis_coefficients_slice)
        .copied()
        .collect()
}

pub fn pack_scalars_to_extension<F: Field, EF: ExtensionField<F>>(scalars: &[F]) -> Vec<EF> {
    let extension_size = <EF as BasedVectorSpace<F>>::DIMENSION;
    assert!(
        scalars.len().is_multiple_of(extension_size),
        "Scalars length must be a multiple of the extension size"
    );
    scalars
        .chunks_exact(extension_size)
        .map(|chunk| EF::from_basis_coefficients_slice(chunk).unwrap())
        .collect()
}

/// Expand a bare polynomial h(X) into the full polynomial g(X) = eq(α, X) * h(X).
/// eq(α, X) = X*α + (1-X)*(1-α) = (1-α) + (2α-1)*X
pub fn expand_bare_to_full<EF: Field>(bare: &[EF], alpha: EF) -> Vec<EF> {
    let one_minus_alpha = EF::ONE - alpha;
    let two_alpha_minus_one = alpha.double() - EF::ONE;
    let d = bare.len() - 1; // degree of bare polynomial
    let mut full = Vec::with_capacity(bare.len() + 1);
    full.push(one_minus_alpha * bare[0]);
    for k in 1..=d {
        full.push(one_minus_alpha * bare[k] + two_alpha_minus_one * bare[k - 1]);
    }
    full.push(two_alpha_minus_one * bare[d]);
    full
}

pub(crate) fn sample_vec<F: PrimeField64, EF: ExtensionField<F>, P: Compression<[F; WIDTH]>>(
    challenger: &mut Challenger<F, P>,
    len: usize,
) -> Vec<EF> {
    let sampled_fe = challenger
        .sample_many((len * EF::DIMENSION).div_ceil(RATE))
        .into_iter()
        .flatten()
        .take(len * EF::DIMENSION)
        .collect::<Vec<F>>();
    let mut res = Vec::new();
    for chunk in sampled_fe.chunks(EF::DIMENSION) {
        res.push(EF::from_basis_coefficients_slice(chunk).unwrap());
    }
    res
}
