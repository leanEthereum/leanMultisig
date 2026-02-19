// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::PrimeCharacteristicRing;

pub(crate) const fn bits_u64(n: u64) -> usize {
    (64 - n.leading_zeros()) as usize
}

/// Compute the exponential `x -> x^1420470955` using a custom addition chain.
///
/// This map computes the third root of `x` if `x` is a member of the field `KoalaBear`.
/// This follows from the computation: `3 * 1420470955 = 2*(2^31 - 2^24) + 1 = 1 mod (p - 1)`.
#[must_use]
pub fn exp_1420470955<R: PrimeCharacteristicRing>(val: R) -> R {
    // Note the binary expansion: 1420470955 = 1010100101010101010101010101011_2
    // This uses 29 Squares + 7 Multiplications => 36 Operations total.
    // Suspect it's possible to improve this with enough effort.
    let p1 = val;
    let p100 = p1.exp_power_of_2(2);
    let p101 = p100.clone() * p1.clone();
    let p10000 = p100.exp_power_of_2(2);
    let p10101 = p10000 * p101;
    let p10101000000 = p10101.exp_power_of_2(6);
    let p10101010101 = p10101000000.clone() * p10101.clone();
    let p101010010101 = p10101000000 * p10101010101.clone();
    let p101010010101000000000000 = p101010010101.exp_power_of_2(12);
    let p101010010101010101010101 = p101010010101000000000000 * p10101010101;
    let p101010010101010101010101000000 = p101010010101010101010101.exp_power_of_2(6);
    let p101010010101010101010101010101 = p101010010101010101010101000000 * p10101;
    let p1010100101010101010101010101010 = p101010010101010101010101010101.square();
    p1010100101010101010101010101010 * p1
}
