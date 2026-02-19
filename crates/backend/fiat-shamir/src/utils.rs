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
