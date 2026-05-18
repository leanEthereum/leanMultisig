// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use core::arch::aarch64::{int32x4_t, uint32x4_t};
use core::mem::transmute;

use crate::{MontyParametersNeon, PackedMontyField31Neon};

use crate::KoalaBearParameters;

const WIDTH: usize = 4;

impl MontyParametersNeon for KoalaBearParameters {
    const PACKED_P: uint32x4_t = unsafe { transmute::<[u32; WIDTH], _>([0xfa000001; WIDTH]) };
    // MU = 0x06000001, which fits in positive i32.
    const PACKED_MU: int32x4_t = unsafe { transmute::<[i32; WIDTH], _>([0x06000001_i32; WIDTH]) };
}

pub type PackedKoalaBearNeon = PackedMontyField31Neon<KoalaBearParameters>;

#[cfg(test)]
mod tests {
    use crate::{KoalaBear, PackedKoalaBearNeon};
    use field::{PrimeCharacteristicRing, PrimeField32};

    fn assert_packed_broadcast_dot_product_matches_scalar<const N: usize>(lhs_raw: [u32; N], rhs_raw: [u32; N]) {
        let lhs: [KoalaBear; N] = lhs_raw.map(KoalaBear::new);
        let rhs: [KoalaBear; N] = rhs_raw.map(KoalaBear::new);

        let scalar_ref = KoalaBear::dot_product::<N>(&lhs, &rhs);

        let packed_lhs: [PackedKoalaBearNeon; N] = lhs.map(PackedKoalaBearNeon::from);
        let packed_rhs: [PackedKoalaBearNeon; N] = rhs.map(PackedKoalaBearNeon::from);
        let packed = PackedKoalaBearNeon::dot_product::<N>(&packed_lhs, &packed_rhs);

        let lanes: [KoalaBear; 4] = packed.0;
        for (lane, got) in lanes.iter().enumerate() {
            assert_eq!(
                *got, scalar_ref,
                "lane {lane}: packed dot_product::<{N}> mismatch — lhs={lhs_raw:?} rhs={rhs_raw:?}",
            );
        }
    }

    #[test]
    fn dot_product_5_carry_cascade_regression() {
        const P: u32 = KoalaBear::ORDER_U32;
        let lhs = [P - 1, 1, 8, P - 3, P - 2];
        let rhs = [P - 4, 9, P - 2, P - 5, 6];
        assert_packed_broadcast_dot_product_matches_scalar::<5>(lhs, rhs);
    }
}
