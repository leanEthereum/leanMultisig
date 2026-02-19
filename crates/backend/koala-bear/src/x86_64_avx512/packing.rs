// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use core::arch::x86_64::__m512i;
use core::mem::transmute;

use crate::KoalaBearParameters;
use crate::{MontyParametersAVX512, PackedMontyField31AVX512};

pub type PackedKoalaBearAVX512 = PackedMontyField31AVX512<KoalaBearParameters>;

const WIDTH: usize = 16;

impl MontyParametersAVX512 for KoalaBearParameters {
    const PACKED_P: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x7f000001; WIDTH]) };
    const PACKED_MU: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x81000001; WIDTH]) };
}
