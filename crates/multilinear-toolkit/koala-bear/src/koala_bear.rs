// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use crate::monty_31::{
    BarrettParameters, FieldParameters, MontyField31, MontyParameters, PackedMontyParameters, RelativelyPrimePower,
    TwoAdicData,
};
use field::PrimeCharacteristicRing;
use field::exponentiation::exp_1420470955;

/// The prime field `2^31 - 2^24 + 1`, a.k.a. the Koala Bear field.
pub type KoalaBear = MontyField31<KoalaBearParameters>;

#[derive(Copy, Clone, Default, Debug, Eq, Hash, PartialEq)]
pub struct KoalaBearParameters;

impl MontyParameters for KoalaBearParameters {
    /// The KoalaBear prime: 2^31 - 2^24 + 1
    /// This is a 31-bit prime with the highest possible two adicity if we additionally demand that
    /// the cube map (x -> x^3) is an automorphism of the multiplicative group.
    /// It's not unique, as there is one other option with equal 2 adicity: 2^30 + 2^27 + 2^24 + 1.
    /// There is also one 29-bit prime with higher two adicity which might be appropriate for some applications: 2^29 - 2^26 + 1.
    const PRIME: u32 = 0x7f000001;

    const MONTY_BITS: u32 = 32;
    const MONTY_MU: u32 = 0x81000001;
}

impl PackedMontyParameters for KoalaBearParameters {}

impl BarrettParameters for KoalaBearParameters {}

impl FieldParameters for KoalaBearParameters {
    const MONTY_GEN: KoalaBear = KoalaBear::new(3);
}

impl RelativelyPrimePower<3> for KoalaBearParameters {
    /// In the field `KoalaBear`, `a^{1/3}` is equal to a^{1420470955}.
    ///
    /// This follows from the calculation `3 * 1420470955 = 2*(2^31 - 2^24) + 1 = 1 mod (p - 1)`.
    fn exp_root_d<R: PrimeCharacteristicRing>(val: R) -> R {
        exp_1420470955(val)
    }
}

impl TwoAdicData for KoalaBearParameters {
    const TWO_ADICITY: usize = 24;

    type ArrayLike = &'static [KoalaBear];

    const TWO_ADIC_GENERATORS: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x7f000000, 0x7e010002, 0x6832fe4a, 0x8dbd69c, 0xa28f031, 0x5c4a5b99, 0x29b75a80, 0x17668b8a, 0x27ad539b,
        0x334d48c7, 0x7744959c, 0x768fc6fa, 0x303964b2, 0x3e687d4d, 0x45a60e61, 0x6e2f4d7a, 0x163bd499, 0x6c4a8a45,
        0x143ef899, 0x514ddcad, 0x484ef19b, 0x205d63c3, 0x68e7dd49, 0x6ac49f88,
    ]);

    const ROOTS_8: Self::ArrayLike = &KoalaBear::new_array([0x1, 0x6832fe4a, 0x7e010002, 0x174e3650]);
    const INV_ROOTS_8: Self::ArrayLike = &KoalaBear::new_array([0x1, 0x67b1c9b1, 0xfeffff, 0x16cd01b7]);

    const ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x8dbd69c, 0x6832fe4a, 0x27ae21e2, 0x7e010002, 0x3a89a025, 0x174e3650, 0x27dfce22,
    ]);
    const INV_ROOTS_16: Self::ArrayLike = &KoalaBear::new_array([
        0x1, 0x572031df, 0x67b1c9b1, 0x44765fdc, 0xfeffff, 0x5751de1f, 0x16cd01b7, 0x76242965,
    ]);
}
