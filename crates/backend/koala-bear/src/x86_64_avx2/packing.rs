// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use core::arch::x86_64::__m256i;
use core::mem::transmute;

use crate::KoalaBearParameters;
use crate::{MontyParametersAVX2, PackedMontyField31AVX2};

pub type PackedKoalaBearAVX2 = PackedMontyField31AVX2<KoalaBearParameters>;

const WIDTH: usize = 8;

impl MontyParametersAVX2 for KoalaBearParameters {
    const PACKED_P: __m256i = unsafe { transmute::<[u32; WIDTH], _>([0x7f000001; WIDTH]) };
    const PACKED_MU: __m256i = unsafe { transmute::<[u32; WIDTH], _>([0x81000001; WIDTH]) };
}
