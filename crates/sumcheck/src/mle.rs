use crate::SumcheckComputation;
use crate::SumcheckComputationPacked;
use p3_field::ExtensionField;
use p3_field::PackedFieldExtension;
use p3_field::PackedValue;
use p3_field::PrimeCharacteristicRing;
use p3_util::log2_strict_usize;
use rayon::prelude::*;
use utils::batch_fold_multilinear_in_large_field;
use utils::batch_fold_multilinear_in_large_field_packed;
use utils::pack_extension;
use utils::unpack_extension;
use utils::{EFPacking, PF, PFPacking, packing_width};
use whir_p3::utils::uninitialized_vec;

#[derive(Debug, Clone)]
pub enum Mle<EF: ExtensionField<PF<EF>>> {
    Base(Vec<PF<EF>>),
    Extension(Vec<EF>),
    PackedBase(Vec<PFPacking<EF>>),
    ExtensionPacked(Vec<EFPacking<EF>>),
}

#[derive(Debug)]
pub enum MleGroup<'a, EF: ExtensionField<PF<EF>>> {
    Owned(MleGroupOwned<EF>),
    Ref(MleGroupRef<'a, EF>),
}

impl<'a, EF: ExtensionField<PF<EF>>> From<MleGroupOwned<EF>> for MleGroup<'a, EF> {
    fn from(owned: MleGroupOwned<EF>) -> Self {
        MleGroup::Owned(owned)
    }
}

impl<'a, EF: ExtensionField<PF<EF>>> From<MleGroupRef<'a, EF>> for MleGroup<'a, EF> {
    fn from(r: MleGroupRef<'a, EF>) -> Self {
        MleGroup::Ref(r)
    }
}

#[derive(Debug)]
pub enum MleGroupOwned<EF: ExtensionField<PF<EF>>> {
    Base(Vec<Vec<PF<EF>>>),
    Extension(Vec<Vec<EF>>),
    BasePacked(Vec<Vec<PFPacking<EF>>>),
    ExtensionPacked(Vec<Vec<EFPacking<EF>>>),
}

#[derive(Clone, Debug)]
pub enum MleGroupRef<'a, EF: ExtensionField<PF<EF>>> {
    Base(Vec<&'a [PF<EF>]>),
    Extension(Vec<&'a [EF]>),
    BasePacked(Vec<&'a [PFPacking<EF>]>),
    ExtensionPacked(Vec<&'a [EFPacking<EF>]>),
}

impl<'a, EF: ExtensionField<PF<EF>>> MleGroup<'a, EF> {
    pub fn by_ref(&'a self) -> MleGroupRef<'a, EF> {
        match self {
            Self::Owned(owned) => owned.by_ref(),
            Self::Ref(r) => r.clone(),
        }
    }

    pub fn n_vars(&self) -> usize {
        match self {
            Self::Owned(owned) => owned.n_vars(),
            Self::Ref(r) => r.n_vars(),
        }
    }

    pub const fn n_columns(&self) -> usize {
        match self {
            Self::Owned(owned) => owned.n_columns(),
            Self::Ref(r) => r.n_columns(),
        }
    }
}

impl<EF: ExtensionField<PF<EF>>> MleGroupOwned<EF> {
    pub fn by_ref<'a>(&'a self) -> MleGroupRef<'a, EF> {
        match self {
            Self::Base(base) => MleGroupRef::Base(base.iter().map(|v| v.as_slice()).collect()),
            Self::Extension(ext) => {
                MleGroupRef::Extension(ext.iter().map(|v| v.as_slice()).collect())
            }
            Self::BasePacked(packed_base) => {
                MleGroupRef::BasePacked(packed_base.iter().map(|v| v.as_slice()).collect())
            }
            Self::ExtensionPacked(ext_packed) => {
                MleGroupRef::ExtensionPacked(ext_packed.iter().map(|v| v.as_slice()).collect())
            }
        }
    }

    pub fn n_vars(&self) -> usize {
        match self {
            Self::Base(v) => log2_strict_usize(v[0].len()),
            Self::Extension(v) => log2_strict_usize(v[0].len()),
            Self::BasePacked(v) => log2_strict_usize(v[0].len() * packing_width::<EF>()),
            Self::ExtensionPacked(v) => log2_strict_usize(v[0].len() * packing_width::<EF>()),
        }
    }

    pub const fn n_columns(&self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Extension(v) => v.len(),
            Self::BasePacked(v) => v.len(),
            Self::ExtensionPacked(v) => v.len(),
        }
    }
}

impl<EF: ExtensionField<PF<EF>>> Mle<EF> {
    pub const fn packed_len(&self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Extension(v) => v.len(),
            Self::PackedBase(v) => v.len(),
            Self::ExtensionPacked(v) => v.len(),
        }
    }

    pub const fn unpacked_len(&self) -> usize {
        let mut res = self.packed_len();
        if self.is_packed() {
            res *= packing_width::<EF>();
        }
        res
    }

    pub fn n_vars(&self) -> usize {
        log2_strict_usize(self.unpacked_len())
    }

    pub fn truncate(&mut self, new_packed_len: usize) {
        match self {
            Self::Base(v) => v.truncate(new_packed_len),
            Self::Extension(v) => v.truncate(new_packed_len),
            Self::PackedBase(v) => v.truncate(new_packed_len),
            Self::ExtensionPacked(v) => v.truncate(new_packed_len),
        }
    }

    pub const fn is_packed(&self) -> bool {
        match self {
            Self::Base(_) | Self::Extension(_) => false,
            Self::PackedBase(_) | Self::ExtensionPacked(_) => true,
        }
    }

    pub const fn as_base(&self) -> Option<&Vec<PF<EF>>> {
        match self {
            Self::Base(b) => Some(b),
            _ => None,
        }
    }

    pub const fn as_extension(&self) -> Option<&Vec<EF>> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub const fn as_packed_base(&self) -> Option<&Vec<PFPacking<EF>>> {
        match self {
            Self::PackedBase(pb) => Some(pb),
            _ => None,
        }
    }

    pub const fn as_extension_packed(&self) -> Option<&Vec<EFPacking<EF>>> {
        match self {
            Self::ExtensionPacked(ep) => Some(ep),
            _ => None,
        }
    }
}

impl<'a, EF: ExtensionField<PF<EF>>> MleGroupRef<'a, EF> {
    pub const fn group_size(&self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Extension(v) => v.len(),
            Self::BasePacked(v) => v.len(),
            Self::ExtensionPacked(v) => v.len(),
        }
    }

    pub fn n_vars(&self) -> usize {
        match self {
            Self::Base(v) => log2_strict_usize(v[0].len()),
            Self::Extension(v) => log2_strict_usize(v[0].len()),
            Self::BasePacked(v) => log2_strict_usize(v[0].len() * packing_width::<EF>()),
            Self::ExtensionPacked(v) => log2_strict_usize(v[0].len() * packing_width::<EF>()),
        }
    }

    pub const fn is_packed(&self) -> bool {
        match self {
            Self::BasePacked(_) | Self::ExtensionPacked(_) => true,
            Self::Base(_) | Self::Extension(_) => false,
        }
    }

    pub const fn as_base(&self) -> Option<&Vec<&'a [PF<EF>]>> {
        match self {
            Self::Base(b) => Some(b),
            _ => None,
        }
    }

    pub const fn as_extension(&self) -> Option<&Vec<&'a [EF]>> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub const fn as_packed_base(&self) -> Option<&Vec<&'a [PFPacking<EF>]>> {
        match self {
            Self::BasePacked(pb) => Some(pb),
            _ => None,
        }
    }

    pub const fn as_extension_packed(&self) -> Option<&Vec<&'a [EFPacking<EF>]>> {
        match self {
            Self::ExtensionPacked(ep) => Some(ep),
            _ => None,
        }
    }

    pub const fn n_columns(&self) -> usize {
        match self {
            Self::Base(v) => v.len(),
            Self::Extension(v) => v.len(),
            Self::BasePacked(v) => v.len(),
            Self::ExtensionPacked(v) => v.len(),
        }
    }

    pub fn pack(&self) -> MleGroup<'a, EF> {
        match self {
            Self::Base(base) => MleGroupRef::BasePacked(
                base.iter()
                    .map(|v| PFPacking::<EF>::pack_slice(v))
                    .collect(),
            )
            .into(),
            Self::Extension(ext) => {
                // the only case where there is real work
                MleGroupOwned::ExtensionPacked(ext.iter().map(|v| pack_extension(v)).collect())
                    .into()
            }
            Self::BasePacked(_) | Self::ExtensionPacked(_) => self.clone().into(),
        }
    }

    // Clone everything in the group, should not be used when n_vars is large
    pub fn unpack(&self) -> MleGroupOwned<EF> {
        match self {
            Self::Base(pols) => MleGroupOwned::Base(pols.iter().map(|v| v.to_vec()).collect()),
            Self::Extension(pols) => {
                MleGroupOwned::Extension(pols.iter().map(|v| v.to_vec()).collect())
            }
            Self::BasePacked(pols) => MleGroupOwned::Base(
                pols.iter()
                    .map(|v| PFPacking::<EF>::unpack_slice(v).to_vec())
                    .collect(),
            ),
            Self::ExtensionPacked(pols) => {
                MleGroupOwned::Extension(pols.iter().map(|v| unpack_extension(v)).collect())
            }
        }
    }

    pub fn fold_in_large_field(&self, scalars: &[EF]) -> MleGroupOwned<EF> {
        match self {
            Self::Base(pols) => {
                MleGroupOwned::Extension(batch_fold_multilinear_in_large_field(pols, scalars))
            }
            Self::Extension(pols) => {
                MleGroupOwned::Extension(batch_fold_multilinear_in_large_field(pols, scalars))
            }
            Self::BasePacked(pols) => MleGroupOwned::ExtensionPacked(
                // TODO this is ugly and not optimized
                batch_fold_multilinear_in_large_field(
                    &pols
                        .iter()
                        .copied()
                        .map(PFPacking::<EF>::unpack_slice)
                        .collect::<Vec<_>>(),
                    scalars,
                )
                .iter()
                .map(|m| pack_extension(m))
                .collect(),
            ),
            Self::ExtensionPacked(pols) => MleGroupOwned::ExtensionPacked(
                batch_fold_multilinear_in_large_field_packed(pols, scalars),
            ),
        }
    }

    pub fn sumcheck_compute<SC, SCP>(
        &self,
        zs: &[usize],
        skips: usize,
        eq_mle: Option<&Mle<EF>>,
        folding_scalars: &[Vec<PF<EF>>],
        computation: &SC,
        computation_packed: &SCP,
        batching_scalars: &[EF],
        missing_mul_factor: Option<EF>,
    ) -> Vec<(PF<EF>, EF)>
    where
        SC: SumcheckComputation<PF<EF>, EF> + SumcheckComputation<EF, EF>,
        SCP: SumcheckComputationPacked<EF>,
    {
        let fold_size = 1 << (self.n_vars() - skips);
        let packed_fold_size = if self.is_packed() {
            fold_size / packing_width::<EF>()
        } else {
            fold_size
        };

        match self {
            Self::ExtensionPacked(multilinears) => {
                let eq_mle = eq_mle.map(|eq_mle| eq_mle.as_extension_packed().unwrap());
                let all_sums =
                    unsafe { uninitialized_vec::<EFPacking<EF>>(zs.len() * packed_fold_size) }; // sums for zs[0], sums for zs[1], ...
                (0..packed_fold_size).into_par_iter().for_each(|i| {
                    let eq_mle_eval = eq_mle.as_ref().map(|eq_mle| eq_mle[i]);
                    let rows = multilinears
                        .iter()
                        .map(|m| {
                            (0..1 << skips)
                                .map(|j| m[i + j * packed_fold_size])
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    for (z_index, folding_scalars_z) in folding_scalars.iter().enumerate() {
                        let point = rows
                            .iter()
                            .map(|row| {
                                row.iter()
                                    .zip(folding_scalars_z.iter())
                                    .map(|(x, s)| *x * PFPacking::<EF>::from(*s))
                                    .sum::<EFPacking<EF>>()
                            })
                            .collect::<Vec<_>>();

                        let mut res =
                            computation_packed.eval_packed_extension(&point, batching_scalars);
                        if let Some(eq_mle_eval) = eq_mle_eval {
                            res *= eq_mle_eval;
                        }

                        unsafe {
                            let sum_ptr = all_sums.as_ptr() as *mut EFPacking<EF>;
                            *sum_ptr.add(z_index * packed_fold_size + i) = res;
                        }
                    }
                });

                let mut evals = vec![];
                for (z_index, z) in zs.iter().enumerate() {
                    let mut sum_z = all_sums
                        [z_index * packed_fold_size..(z_index + 1) * packed_fold_size]
                        .par_iter()
                        .copied()
                        .sum::<EFPacking<EF>>();
                    if let Some(missing_mul_factor) = missing_mul_factor {
                        sum_z *= missing_mul_factor;
                    }
                    evals.push((
                        PF::<EF>::from_usize(*z),
                        EFPacking::<EF>::to_ext_iter([sum_z]).sum::<EF>(),
                    ));
                }
                evals
            }
            Self::BasePacked(multilinears) => {
                let eq_mle = eq_mle.map(|eq_mle| eq_mle.as_extension_packed().unwrap());

                let all_sums =
                    unsafe { uninitialized_vec::<EFPacking<EF>>(zs.len() * packed_fold_size) }; // sums for zs[0], sums for zs[1], ...
                (0..packed_fold_size).into_par_iter().for_each(|i| {
                    let eq_mle_eval = eq_mle.as_ref().map(|eq_mle| eq_mle[i]);
                    let rows = multilinears
                        .iter()
                        .map(|m| {
                            (0..1 << skips)
                                .map(|j| m[i + j * packed_fold_size])
                                .collect::<Vec<_>>()
                        })
                        .collect::<Vec<_>>();
                    for (z_index, folding_scalars_z) in folding_scalars.iter().enumerate() {
                        let point = rows
                            .iter()
                            .map(|row| {
                                row.iter()
                                    .zip(folding_scalars_z.iter())
                                    .map(|(x, s)| *x * *s)
                                    .sum::<PFPacking<EF>>()
                            })
                            .collect::<Vec<_>>();

                        let mut res = computation_packed.eval_packed_base(&point, batching_scalars);
                        if let Some(eq_mle_eval) = eq_mle_eval {
                            res *= eq_mle_eval;
                        }

                        unsafe {
                            let sum_ptr = all_sums.as_ptr() as *mut EFPacking<EF>;
                            *sum_ptr.add(z_index * packed_fold_size + i) = res;
                        }
                    }
                });

                let mut evals = vec![];
                for (z_index, z) in zs.iter().enumerate() {
                    let sum_z_packed = all_sums
                        [z_index * packed_fold_size..(z_index + 1) * packed_fold_size]
                        .par_iter()
                        .copied()
                        .sum::<EFPacking<EF>>();
                    let mut sum_z = EFPacking::<EF>::to_ext_iter([sum_z_packed]).sum::<EF>();
                    if let Some(missing_mul_factor) = missing_mul_factor {
                        sum_z *= missing_mul_factor;
                    }
                    evals.push((PF::<EF>::from_usize(*z), sum_z));
                }
                evals
            }
            Self::Base(multilinears) => {
                let eq_mle = eq_mle.map(|eq_mle| eq_mle.as_extension().unwrap().as_slice());
                sumcheck_compute_not_packed(
                    multilinears,
                    zs,
                    skips,
                    eq_mle,
                    folding_scalars,
                    computation,
                    batching_scalars,
                    missing_mul_factor,
                    fold_size,
                )
            }
            Self::Extension(multilinears) => {
                let eq_mle = eq_mle.map(|eq_mle| eq_mle.as_extension().unwrap().as_slice());
                sumcheck_compute_not_packed(
                    multilinears,
                    zs,
                    skips,
                    eq_mle,
                    folding_scalars,
                    computation,
                    batching_scalars,
                    missing_mul_factor,
                    fold_size,
                )
            }
        }
    }
}

pub fn sumcheck_compute_not_packed<
    EF: ExtensionField<PF<EF>> + ExtensionField<IF>,
    IF: ExtensionField<PF<EF>>,
    SC,
>(
    multilinears: &[&[IF]],
    zs: &[usize],
    skips: usize,
    eq_mle: Option<&[EF]>,
    folding_scalars: &[Vec<PF<EF>>],
    computation: &SC,
    batching_scalars: &[EF],
    missing_mul_factor: Option<EF>,
    fold_size: usize,
) -> Vec<(PF<EF>, EF)>
where
    SC: SumcheckComputation<IF, EF>,
{
    let all_sums = unsafe { uninitialized_vec::<EF>(zs.len() * fold_size) }; // sums for zs[0], sums for zs[1], ...
    (0..fold_size).into_par_iter().for_each(|i| {
        let eq_mle_eval = eq_mle.as_ref().map(|eq_mle| eq_mle[i]);
        let rows = multilinears
            .iter()
            .map(|m| {
                (0..1 << skips)
                    .map(|j| m[i + j * fold_size])
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        for (z_index, folding_scalars_z) in folding_scalars.iter().enumerate() {
            let point = rows
                .iter()
                .map(|row| {
                    row.iter()
                        .zip(folding_scalars_z.iter())
                        .map(|(x, s)| *x * *s)
                        .sum::<IF>()
                })
                .collect::<Vec<_>>();
            unsafe {
                let sum_ptr = all_sums.as_ptr() as *mut EF;
                let mut res = computation.eval(&point, batching_scalars);
                if let Some(eq_mle_eval) = eq_mle_eval {
                    res *= eq_mle_eval;
                }
                *sum_ptr.add(z_index * fold_size + i) = res;
            }
        }
    });
    let mut evals = vec![];
    for (z_index, z) in zs.iter().enumerate() {
        let mut sum_z = all_sums[z_index * fold_size..(z_index + 1) * fold_size]
            .par_iter()
            .copied()
            .sum::<EF>();
        if let Some(missing_mul_factor) = missing_mul_factor {
            sum_z *= missing_mul_factor;
        }
        evals.push((PF::<EF>::from_usize(*z), sum_z));
    }
    evals
}
