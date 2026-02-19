use crate::*;
use ::utils::log2_strict_usize;
use field::ExtensionField;

#[derive(Debug)]
pub enum MleGroupOwned<EF: ExtensionField<PF<EF>>> {
    Base(Vec<Vec<PF<EF>>>),
    Extension(Vec<Vec<EF>>),
    BasePacked(Vec<Vec<PFPacking<EF>>>),
    ExtensionPacked(Vec<Vec<EFPacking<EF>>>),
}

impl<EF: ExtensionField<PF<EF>>> MleGroupOwned<EF> {
    pub fn as_extension_mut(&mut self) -> Option<&mut Vec<Vec<EF>>> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_extension_packed_mut(&mut self) -> Option<&mut Vec<Vec<EFPacking<EF>>>> {
        match self {
            Self::ExtensionPacked(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_extension(self) -> Option<Vec<Vec<EF>>> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub fn is_extension(&self) -> bool {
        matches!(self, Self::Extension(_) | Self::ExtensionPacked(_))
    }

    pub fn is_packed(&self) -> bool {
        matches!(self, Self::BasePacked(_) | Self::ExtensionPacked(_))
    }

    pub fn by_ref<'a>(&'a self) -> MleGroupRef<'a, EF> {
        match self {
            Self::Base(base) => MleGroupRef::Base(base.iter().map(|v| v.as_slice()).collect()),
            Self::Extension(ext) => MleGroupRef::Extension(ext.iter().map(|v| v.as_slice()).collect()),
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

    pub fn split(self) -> Vec<MleOwned<EF>> {
        match self {
            Self::Base(v) => v.into_iter().map(|col| MleOwned::Base(col)).collect(),
            Self::Extension(v) => v.into_iter().map(|col| MleOwned::Extension(col)).collect(),
            Self::BasePacked(v) => v.into_iter().map(|col| MleOwned::BasePacked(col)).collect(),
            Self::ExtensionPacked(v) => v.into_iter().map(|col| MleOwned::ExtensionPacked(col)).collect(),
        }
    }

    pub fn merge(mles: Vec<MleOwned<EF>>) -> Self {
        assert!(!mles.is_empty());
        match &mles[0] {
            MleOwned::Base(_) => Self::Base(mles.into_iter().map(|m| m.into_base().unwrap()).collect()),
            MleOwned::Extension(_) => Self::Extension(mles.into_iter().map(|m| m.into_extension().unwrap()).collect()),
            MleOwned::BasePacked(_) => {
                Self::BasePacked(mles.into_iter().map(|m| m.into_base_backed().unwrap()).collect())
            }
            MleOwned::ExtensionPacked(_) => {
                Self::ExtensionPacked(mles.into_iter().map(|m| m.into_extension_packed().unwrap()).collect())
            }
        }
    }

    pub fn empty(extension: bool, packed: bool) -> Self {
        match (extension, packed) {
            (false, false) => Self::Base(Vec::new()),
            (true, false) => Self::Extension(Vec::new()),
            (false, true) => Self::BasePacked(Vec::new()),
            (true, true) => Self::ExtensionPacked(Vec::new()),
        }
    }
}
