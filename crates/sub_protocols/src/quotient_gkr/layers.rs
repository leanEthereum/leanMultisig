use backend::PackedValue;
use std::borrow::Cow;

use backend::*;

pub(super) enum LayerStorage<'a, EF: ExtensionField<PF<EF>>> {
    Initial {
        nums: Cow<'a, [PFPacking<EF>]>,
        dens: Cow<'a, [EFPacking<EF>]>,
        chunk_log: usize,
    },
    PackedBr {
        nums: Cow<'a, [EFPacking<EF>]>,
        dens: Cow<'a, [EFPacking<EF>]>,
        chunk_log: usize,
    },
    Natural {
        nums: Cow<'a, [EF]>,
        dens: Cow<'a, [EF]>,
    },
}

impl<'a, EF: ExtensionField<PF<EF>>> LayerStorage<'a, EF> {
    pub(super) fn convert_to_natural(&self) -> Self {
        match self {
            Self::Initial { nums, dens, chunk_log } => {
                let n_nat: Vec<EF> = bit_reverse_chunks(PFPacking::<EF>::unpack_slice(nums.as_ref()), *chunk_log)
                    .into_iter()
                    .map(EF::from)
                    .collect();
                let d_nat = unpack_and_unreverse_slice(dens.as_ref(), *chunk_log);
                Self::Natural {
                    nums: Cow::Owned(n_nat),
                    dens: Cow::Owned(d_nat),
                }
            }
            Self::PackedBr { nums, dens, chunk_log } => {
                let n_nat = unpack_and_unreverse_slice(nums.as_ref(), *chunk_log);
                let d_nat = unpack_and_unreverse_slice(dens.as_ref(), *chunk_log);
                Self::Natural {
                    nums: Cow::Owned(n_nat),
                    dens: Cow::Owned(d_nat),
                }
            }
            Self::Natural { nums, dens } => Self::Natural {
                nums: Cow::Owned(nums.to_vec()),
                dens: Cow::Owned(dens.to_vec()),
            },
        }
    }

    pub(super) fn natural_nums_dens(&self) -> (&[EF], &[EF]) {
        match self {
            Self::Natural { nums, dens } => (nums.as_ref(), dens.as_ref()),
            _ => unreachable!(),
        }
    }

    pub(super) fn sum_quotients_2_by_2(&self) -> Self {
        match self {
            Self::Initial { nums, dens, chunk_log } => {
                let (new_nums, new_dens) =
                    sum_quotients_2_by_2_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                Self::PackedBr {
                    nums: Cow::Owned(new_nums),
                    dens: Cow::Owned(new_dens),
                    chunk_log: *chunk_log - 1,
                }
            }
            Self::PackedBr { nums, dens, chunk_log } => {
                let (new_nums, new_dens) =
                    sum_quotients_2_by_2_packed_br::<EF, _>(nums.as_ref(), dens.as_ref(), *chunk_log);
                Self::PackedBr {
                    nums: Cow::Owned(new_nums),
                    dens: Cow::Owned(new_dens),
                    chunk_log: *chunk_log - 1,
                }
            }
            Self::Natural { nums, dens } => {
                let (nn, nd) = sum_quotients_2_by_2(nums.as_ref(), dens.as_ref());
                Self::Natural {
                    nums: Cow::Owned(nn),
                    dens: Cow::Owned(nd),
                }
            }
        }
    }

    pub(super) fn chunk_log(&self) -> usize {
        match self {
            Self::Initial { chunk_log, .. } => *chunk_log,
            Self::PackedBr { chunk_log, .. } => *chunk_log,
            Self::Natural { .. } => 0,
        }
    }
}

/// Bit-reverse each `2^chunk_log`-sized chunk of `v` (unpacked, any element
/// type). Bit-reversal is an involution, so this is also its own inverse.
fn bit_reverse_chunks<T: Copy + Send + Sync>(v: &[T], chunk_log: usize) -> Vec<T> {
    let n = v.len();
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    let mut out: Vec<T> = unsafe { uninitialized_vec(n) };
    bit_reverse_chunks_into(v, chunk_log, &mut out);
    out
}

fn bit_reverse_chunks_into<T: Copy + Send + Sync>(v: &[T], chunk_log: usize, out: &mut [T]) {
    let n = v.len();
    assert_eq!(n, out.len());
    debug_assert!(n.is_power_of_two());
    debug_assert!(chunk_log <= n.trailing_zeros() as usize);
    if chunk_log == 0 {
        out.copy_from_slice(v);
        return;
    }
    let chunk_size = 1usize << chunk_log;
    let shift = usize::BITS as usize - chunk_log;
    out.par_chunks_exact_mut(chunk_size)
        .zip(v.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
}

fn sum_quotients_2_by_2<EF: ExtensionField<PF<EF>>>(nums: &[EF], dens: &[EF]) -> (Vec<EF>, Vec<EF>) {
    let n = nums.len();
    assert_eq!(n, dens.len());
    let new_n = n / 2;
    let mut new_nums = unsafe { uninitialized_vec(new_n) };
    let mut new_dens = unsafe { uninitialized_vec(new_n) };
    new_nums
        .par_iter_mut()
        .zip(new_dens.par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            // LSB pairing: combine storage positions 2i and 2i+1.
            let n0 = nums[2 * i];
            let n1 = nums[2 * i + 1];
            let d0 = dens[2 * i];
            let d1 = dens[2 * i + 1];
            *num = d1 * n0 + d0 * n1;
            *den = d0 * d1;
        });
    (new_nums, new_dens)
}

fn sum_quotients_2_by_2_packed_br<EF: ExtensionField<PF<EF>>, N>(
    nums: &[N],
    dens: &[EFPacking<EF>],
    chunk_log: usize,
) -> (Vec<EFPacking<EF>>, Vec<EFPacking<EF>>)
where
    N: Copy + Send + Sync,
    EFPacking<EF>: Algebra<N>,
{
    let w = packing_log_width::<EF>();
    debug_assert!(chunk_log > w);
    debug_assert_eq!(nums.len(), dens.len());

    let bit = chunk_log - 1 - w;
    let stride = 1usize << bit;
    let lo_mask = stride - 1;
    let new_packed_len = nums.len() / 2;

    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_packed_len) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(new_packed_len) };

    new_nums
        .par_iter_mut()
        .zip(new_dens.par_iter_mut())
        .enumerate()
        .for_each(|(new_j, (num_out, den_out))| {
            let i_hi = new_j >> bit;
            let i_lo = new_j & lo_mask;
            let i0 = (i_hi << (bit + 1)) | i_lo;
            let i1 = i0 | stride;
            *num_out = dens[i1] * nums[i0] + dens[i0] * nums[i1];
            *den_out = dens[i0] * dens[i1];
        });

    (new_nums, new_dens)
}

/// Natural-order extension-field slice → chunk-bit-reversed + packed.
pub(super) fn bit_reverse_chunks_and_pack_ext<EF: ExtensionField<PF<EF>>>(
    v: &[EF],
    chunk_log: usize,
) -> Vec<EFPacking<EF>> {
    pack_extension(&bit_reverse_chunks(v, chunk_log)) // TODO do it in one pass without the intermediate Vec
}

/// Base-field analogue: natural-order `&[PF]` → chunk-bit-reversed + packed.
pub(super) fn bit_reverse_chunks_and_pack_base<EF: ExtensionField<PF<EF>>>(
    v: &[PF<EF>],
    chunk_log: usize,
) -> Vec<PFPacking<EF>> {
    let width: usize = packing_width::<EF>();
    let mut res = unsafe { uninitialized_vec::<PFPacking<EF>>(v.len() / width) };
    let unpacked = PFPacking::<EF>::unpack_slice_mut(&mut res);
    bit_reverse_chunks_into(v, chunk_log, unpacked);
    res
}

/// Inverse of `bit_reverse_chunks_and_pack` for ext-packed slices.
pub(super) fn unpack_and_unreverse_slice<EF: ExtensionField<PF<EF>>>(v: &[EFPacking<EF>], chunk_log: usize) -> Vec<EF> {
    bit_reverse_chunks(&unpack_extension::<EF>(v), chunk_log)
}
