use crate::*;
use ::utils::log2_strict_usize;
use field::ExtensionField;
use field::PackedValue;

#[derive(Debug)]
pub enum MleGroupRef<'a, EF: ExtensionField<PF<EF>>> {
    Base(Vec<&'a [PF<EF>]>),
    Extension(Vec<&'a [EF]>),
    BasePacked(Vec<&'a [PFPacking<EF>]>),
    ExtensionPacked(Vec<&'a [EFPacking<EF>]>),
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

    pub fn is_extension(&self) -> bool {
        matches!(self, Self::Extension(_) | Self::ExtensionPacked(_))
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
            Self::Base(base) => {
                MleGroupRef::BasePacked(base.iter().map(|v| PFPacking::<EF>::pack_slice(v)).collect()).into()
            }
            Self::Extension(ext) => {
                // the only case where there is real work
                MleGroupOwned::ExtensionPacked(ext.iter().map(|v| pack_extension(v)).collect()).into()
            }
            Self::BasePacked(_) | Self::ExtensionPacked(_) => self.soft_clone().into(),
        }
    }

    /// performs a "real" clone only in case `Self::ExtensionPacked`
    pub fn unpack(&self) -> MleGroup<'_, EF> {
        match self {
            Self::Base(_) | Self::Extension(_) => self.soft_clone().into(),
            Self::BasePacked(pols) => {
                MleGroupRef::Base(pols.iter().map(|v| PFPacking::<EF>::unpack_slice(v)).collect()).into()
            }
            Self::ExtensionPacked(pols) => {
                MleGroupOwned::Extension(pols.iter().map(|v| unpack_extension(v)).collect()).into()
            }
        }
    }

    pub fn fold(&self, alpha: EF) -> MleGroupOwned<EF> {
        match self {
            Self::Base(pols) => MleGroupOwned::Extension(batch_fold_multilinears(pols, alpha, |a, b| b * a)),
            Self::Extension(pols) => MleGroupOwned::Extension(batch_fold_multilinears(pols, alpha, |a, b| b * a)),
            Self::BasePacked(pols) => {
                let alpha_packed = EFPacking::<EF>::from(alpha);
                MleGroupOwned::ExtensionPacked(batch_fold_multilinears(pols, alpha_packed, |a, b| b * a))
            }
            Self::ExtensionPacked(pols) => {
                MleGroupOwned::ExtensionPacked(batch_fold_multilinears(pols, alpha, |a, b| a * b))
            }
        }
    }

    pub fn merge(mles: &'a [&'a MleRef<'a, EF>]) -> Self {
        match &mles[0] {
            MleRef::Base(_) => Self::Base(mles.iter().map(|m| m.as_base().unwrap()).collect()),
            MleRef::Extension(_) => Self::Extension(mles.iter().map(|m| m.as_extension().unwrap()).collect()),
            MleRef::BasePacked(_) => Self::BasePacked(mles.iter().map(|m| m.as_packed_base().unwrap()).collect()),
            MleRef::ExtensionPacked(_) => {
                Self::ExtensionPacked(mles.iter().map(|m| m.as_extension_packed().unwrap()).collect())
            }
        }
    }

    pub fn soft_clone(&self) -> MleGroupRef<'a, EF> {
        match self {
            Self::Base(v) => MleGroupRef::Base(v.clone()),
            Self::Extension(v) => MleGroupRef::Extension(v.clone()),
            Self::BasePacked(v) => MleGroupRef::BasePacked(v.clone()),
            Self::ExtensionPacked(v) => MleGroupRef::ExtensionPacked(v.clone()),
        }
    }

    pub fn clone_to_owned(&self) -> MleGroupOwned<EF> {
        match self {
            Self::Base(pols) => MleGroupOwned::Base(pols.iter().map(|v| v.to_vec()).collect()),
            Self::Extension(pols) => MleGroupOwned::Extension(pols.iter().map(|v| v.to_vec()).collect()),
            Self::BasePacked(pols) => MleGroupOwned::BasePacked(pols.iter().map(|v| v.to_vec()).collect()),
            Self::ExtensionPacked(pols) => MleGroupOwned::ExtensionPacked(pols.iter().map(|v| v.to_vec()).collect()),
        }
    }
}
