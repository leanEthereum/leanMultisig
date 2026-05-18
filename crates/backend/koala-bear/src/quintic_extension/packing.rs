// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::KoalaBear;

/// If no packings are available, we use the generic binomial extension multiplication functions.
///
#[cfg(not(any(
    all(target_arch = "aarch64", target_feature = "neon"),
    all(target_arch = "x86_64", target_feature = "avx2",)
)))]
#[inline]
pub(crate) fn quintic_mul_packed(a: &[KoalaBear; 5], b: &[KoalaBear; 5], res: &mut [KoalaBear; 5]) {
    use field::PrimeCharacteristicRing;
    *res = super::extension::quintic_mul(a, b, KoalaBear::dot_product::<5>);
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx2", not(target_feature = "avx512f")))]
/// Multiplication in a quintic binomial extension field F[X]/(X^5 + 2).
///
/// The packed (vectorized) AVX dot-product helpers used by previous
/// implementations assume P < 2^31. With the current 32-bit prime
/// (P = 0xfa000001 ≈ 2^32), summing two 32-bit-prime products in a u64
/// can overflow, so we route this multiplication through the scalar
/// path which uses u128 accumulation.
#[inline]
pub(crate) fn quintic_mul_packed(a: &[KoalaBear; 5], b: &[KoalaBear; 5], res: &mut [KoalaBear; 5]) {
    use field::PrimeCharacteristicRing;
    *res = super::extension::quintic_mul(a, b, KoalaBear::dot_product::<5>);
}

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f"))]
/// Multiplication in a quintic binomial extension field F[X]/(X^5 + 2).
///
/// The packed (vectorized) AVX dot-product helpers used by previous
/// implementations assume P < 2^31. With the current 32-bit prime
/// (P = 0xfa000001 ≈ 2^32), summing two 32-bit-prime products in a u64
/// can overflow, so we route this multiplication through the scalar
/// path which uses u128 accumulation.
#[inline]
pub(crate) fn quintic_mul_packed(a: &[KoalaBear; 5], b: &[KoalaBear; 5], res: &mut [KoalaBear; 5]) {
    use field::PrimeCharacteristicRing;
    *res = super::extension::quintic_mul(a, b, KoalaBear::dot_product::<5>);
}

#[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
/// Multiplication in quintic extension field F[X]/(X^5 + 2).
#[inline]
pub(crate) fn quintic_mul_packed(a: &[KoalaBear; 5], b: &[KoalaBear; 5], res: &mut [KoalaBear; 5]) {
    use crate::PackedMontyField31Neon;
    use field::PrimeCharacteristicRing;

    // For X^5 + 2: X^5 = -2
    let neg_2b1 = -(b[1] + b[1]);
    let neg_2b2 = -(b[2] + b[2]);
    let neg_2b3 = -(b[3] + b[3]);
    let neg_2b4 = -(b[4] + b[4]);

    let lhs: [PackedMontyField31Neon<crate::KoalaBearParameters>; 5] =
        [a[0].into(), a[1].into(), a[2].into(), a[3].into(), a[4].into()];
    let rhs = [
        PackedMontyField31Neon([b[0], b[1], b[2], b[3]]),
        PackedMontyField31Neon([neg_2b4, b[0], b[1], b[2]]),
        PackedMontyField31Neon([neg_2b3, neg_2b4, b[0], b[1]]),
        PackedMontyField31Neon([neg_2b2, neg_2b3, neg_2b4, b[0]]),
        PackedMontyField31Neon([neg_2b1, neg_2b2, neg_2b3, neg_2b4]),
    ];

    let dot = PackedMontyField31Neon::dot_product(&lhs, &rhs).0;
    res[..4].copy_from_slice(&dot);

    // result[4] = dot(a, [b4, b3, b2, b1, b0])  (no -2 terms)
    res[4] = KoalaBear::dot_product::<5>(&[a[0], a[1], a[2], a[3], a[4]], &[b[4], b[3], b[2], b[1], b[0]]);
}
