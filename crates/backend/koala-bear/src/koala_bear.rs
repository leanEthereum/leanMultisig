// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::monty_31::{
    BarrettParameters, FieldParameters, MontyField31, MontyParameters, PackedMontyParameters, RelativelyPrimePower,
    TwoAdicData,
};
use field::PrimeCharacteristicRing;
use field::exponentiation::exp_2796202667;

/// The prime field `125 * 2^25 + 1 = 4194304001`, a.k.a. the Koala Bear field.
pub type KoalaBear = MontyField31<KoalaBearParameters>;

#[derive(Copy, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct KoalaBearParameters;

impl MontyParameters for KoalaBearParameters {
    /// The KoalaBear prime: 125 * 2^25 + 1 = 4194304001
    /// This is a 32-bit prime with two-adicity 25 and the cube map (x -> x^3) is an
    /// automorphism of the multiplicative group (since gcd(3, p-1) = 1).
    /// Note: the sum of 2 elements does NOT fit in a u32, requiring u64 intermediates for addition.
    const PRIME: u32 = 0xfa000001;

    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x06000001;
}

impl PackedMontyParameters for KoalaBearParameters {}

impl BarrettParameters for KoalaBearParameters {}

impl FieldParameters for KoalaBearParameters {
    const MONTY_GEN: KoalaBear = KoalaBear::new(3);
}

impl RelativelyPrimePower<3> for KoalaBearParameters {
    /// In the field `KoalaBear`, `a^{1/3}` is equal to a^{2796202667}.
    ///
    /// This follows from the calculation `3 * 2796202667 = 8388608001 = 2*(125 * 2^25) + 1 = 1 mod (p - 1)`.
    fn exp_root_d<R: PrimeCharacteristicRing>(val: R) -> R {
        exp_2796202667(val)
    }
}

impl TwoAdicData for KoalaBearParameters {
    const TWO_ADICITY: usize = 25;

    type ArrayLike = &'static [KoalaBear];

    const TWO_ADIC_GENERATORS: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0xfa000000, 0x304096c9, 0x894b5390, 0x6b52061e, 0xad3c2449, 0x15fe844d, 0x78c80fc6, 0x6f53c3e8,
        0xbde222a7, 0xb8d15cfe, 0xeda3085d, 0x796cdd9b, 0xdb8107f4, 0x5e491875, 0xcf40ad0, 0x2526aeba, 0x1df6fb4c,
        0x2f221af1, 0x40593728, 0xcd1100d7, 0x64a4ed0b, 0x9782cd0e, 0xaf03bc88, 0x99d352d0, 0x4633584e,
    ]);

    const ROOTS_8: Self::ArrayLike = &KoalaBear::new_array([0x1, 0x894b5390, 0x304096c9, 0x2e9b3a27]);
    const INV_ROOTS_8: Self::ArrayLike = &KoalaBear::new_array([0x1, 0xcb64c5da, 0xc9bf6938, 0x70b4ac71]);

    const ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x6b52061e, 0x894b5390, 0x39f910ef, 0x304096c9, 0x33c5a441, 0x2e9b3a27, 0x9d09df4b,
    ]);
    const INV_ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x5cf620b6, 0xcb64c5da, 0xc63a5bc0, 0xc9bf6938, 0xc006ef12, 0x70b4ac71, 0x8eadf9e3,
    ]);
}
