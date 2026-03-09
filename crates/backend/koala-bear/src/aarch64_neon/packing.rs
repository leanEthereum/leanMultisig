// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use core::arch::aarch64::{int32x4_t, uint32x4_t};
use core::mem::transmute;

use crate::{MontyParametersNeon, PackedMontyField31Neon};

use crate::KoalaBearParameters;

const WIDTH: usize = 4;

impl MontyParametersNeon for KoalaBearParameters {
    const PACKED_P: uint32x4_t = unsafe { transmute::<[u32; WIDTH], _>([0x7f000001; WIDTH]) };
    // This MU is the same 0x88000001 as elsewhere, just interpreted as an `i32`.
    const PACKED_MU: int32x4_t = unsafe { transmute::<[i32; WIDTH], _>([-0x7effffff; WIDTH]) };
}

pub type PackedKoalaBearNeon = PackedMontyField31Neon<KoalaBearParameters>;
