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
                let n_nat_base: Vec<EF> = unpack_base_and_unreverse_active::<EF>(nums.as_ref(), *chunk_log);
                let d_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), *chunk_log);
                Self::Natural {
                    nums: Cow::Owned(n_nat_base),
                    dens: Cow::Owned(d_nat),
                }
            }
            Self::PackedBr { nums, dens, chunk_log } => {
                let n_nat = unpack_and_unreverse_active::<EF>(nums.as_ref(), *chunk_log);
                let d_nat = unpack_and_unreverse_active::<EF>(dens.as_ref(), *chunk_log);
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

    pub(super) fn materialise_in_full(self) -> (Vec<EF>, Vec<EF>) {
        let natural = match self {
            Self::Natural { .. } => self,
            other => other.convert_to_natural(),
        };
        let Self::Natural { nums, dens } = natural else {
            unreachable!()
        };
        let mut n = nums.into_owned();
        let mut d = dens.into_owned();
        let full = n.len().next_power_of_two();
        n.resize(full, EF::ZERO);
        d.resize(full, EF::ONE);
        (n, d)
    }
}

pub(super) fn bit_reverse_chunks<T: Copy + Send + Sync>(v: &[T], chunk_log: usize) -> Vec<T> {
    let n = v.len();
    let chunk_size = 1usize << chunk_log;
    debug_assert!(n.is_multiple_of(chunk_size));
    let mut out: Vec<T> = unsafe { uninitialized_vec(n) };
    if chunk_log == 0 {
        out.copy_from_slice(v);
        return out;
    }
    let shift = usize::BITS as usize - chunk_log;
    out.par_chunks_exact_mut(chunk_size)
        .zip(v.par_chunks_exact(chunk_size))
        .for_each(|(dst, src)| {
            for (p, slot) in dst.iter_mut().enumerate() {
                *slot = src[p.reverse_bits() >> shift];
            }
        });
    out
}

fn sum_quotients_2_by_2<EF: ExtensionField<PF<EF>>>(nums: &[EF], dens: &[EF]) -> (Vec<EF>, Vec<EF>) {
    assert_eq!(nums.len(), dens.len());
    let active_len = nums.len();
    let new_active = active_len.div_ceil(2);
    let full_pairs = active_len / 2;

    let mut new_nums: Vec<EF> = unsafe { uninitialized_vec(new_active) };
    let mut new_dens: Vec<EF> = unsafe { uninitialized_vec(new_active) };

    new_nums[..full_pairs]
        .par_iter_mut()
        .zip(new_dens[..full_pairs].par_iter_mut())
        .enumerate()
        .for_each(|(i, (num, den))| {
            let n0 = nums[2 * i];
            let n1 = nums[2 * i + 1];
            let d0 = dens[2 * i];
            let d1 = dens[2 * i + 1];
            *num = d1 * n0 + d0 * n1;
            *den = d0 * d1;
        });

    // Boundary (at most one pair: a/b + 0/1 = a/b).
    if full_pairs < new_active {
        new_nums[full_pairs] = nums[2 * full_pairs];
        new_dens[full_pairs] = dens[2 * full_pairs];
    }

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

    let mut new_nums: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(nums.len() >> 1) };
    let mut new_dens: Vec<EFPacking<EF>> = unsafe { uninitialized_vec(nums.len() >> 1) };

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

pub(super) fn unpack_and_unreverse_active<EF: ExtensionField<PF<EF>>>(
    v: &[EFPacking<EF>],
    chunk_log: usize,
) -> Vec<EF> {
    bit_reverse_chunks(&unpack_extension::<EF>(v), chunk_log)
}

fn unpack_base_and_unreverse_active<EF: ExtensionField<PF<EF>>>(v: &[PFPacking<EF>], chunk_log: usize) -> Vec<EF> {
    let active_unpacked: Vec<EF> = PFPacking::<EF>::unpack_slice(v).iter().map(|x| EF::from(*x)).collect();
    bit_reverse_chunks(&active_unpacked, chunk_log)
}
