use field::ExtensionField;

use crate::{EFPacking, Mle, MleRef, MultilinearPoint, PF, PFPacking, pack_extension, unpack_extension};
use field::PackedValue;

#[derive(Debug, Clone)]
pub enum MleOwned<EF: ExtensionField<PF<EF>>> {
    Base(Vec<PF<EF>>),
    Extension(Vec<EF>),
    BasePacked(Vec<PFPacking<EF>>),
    ExtensionPacked(Vec<EFPacking<EF>>),
}

impl<EF: ExtensionField<PF<EF>>> Default for MleOwned<EF> {
    fn default() -> Self {
        Self::Base(vec![])
    }
}

impl<EF: ExtensionField<PF<EF>>> MleOwned<EF> {
    pub fn by_ref<'a>(&'a self) -> MleRef<'a, EF> {
        match self {
            Self::Base(v) => MleRef::Base(v),
            Self::Extension(v) => MleRef::Extension(v),
            Self::BasePacked(v) => MleRef::BasePacked(v),
            Self::ExtensionPacked(v) => MleRef::ExtensionPacked(v),
        }
    }

    pub fn truncate(&mut self, n: usize) {
        match self {
            Self::Base(v) => v.truncate(n),
            Self::Extension(v) => v.truncate(n),
            Self::BasePacked(v) => v.truncate(n),
            Self::ExtensionPacked(v) => v.truncate(n),
        }
    }

    pub fn as_base(&self) -> Option<&[PF<EF>]> {
        match self {
            Self::Base(b) => Some(b),
            _ => None,
        }
    }

    pub fn as_extension(&self) -> Option<&[EF]> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub fn as_packed_base(&self) -> Option<&[PFPacking<EF>]> {
        match self {
            Self::BasePacked(pb) => Some(pb),
            _ => None,
        }
    }

    pub fn as_extension_packed(&self) -> Option<&[EFPacking<EF>]> {
        match self {
            Self::ExtensionPacked(ep) => Some(ep),
            _ => None,
        }
    }

    pub fn as_extension_packed_mut(&mut self) -> Option<&mut Vec<EFPacking<EF>>> {
        match self {
            Self::ExtensionPacked(ep) => Some(ep),
            _ => None,
        }
    }

    pub fn into_base(self) -> Option<Vec<PF<EF>>> {
        match self {
            Self::Base(b) => Some(b),
            _ => None,
        }
    }

    pub fn into_extension(self) -> Option<Vec<EF>> {
        match self {
            Self::Extension(e) => Some(e),
            _ => None,
        }
    }

    pub fn into_base_backed(self) -> Option<Vec<PFPacking<EF>>> {
        match self {
            Self::BasePacked(pb) => Some(pb),
            _ => None,
        }
    }

    pub fn into_extension_packed(self) -> Option<Vec<EFPacking<EF>>> {
        match self {
            Self::ExtensionPacked(ep) => Some(ep),
            _ => None,
        }
    }

    pub fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF {
        self.by_ref().evaluate(point)
    }

    pub fn pack<'a>(&'a self) -> Mle<'a, EF> {
        match self {
            Self::Base(v) => Mle::Ref(MleRef::BasePacked(PFPacking::<EF>::pack_slice(v))),
            Self::Extension(v) => Mle::Owned(MleOwned::ExtensionPacked(pack_extension(v))),
            Self::BasePacked(_) => Mle::Ref(self.by_ref()),
            Self::ExtensionPacked(_) => Mle::Ref(self.by_ref()),
        }
    }

    pub fn unpack<'a>(&'a self) -> Mle<'a, EF> {
        match self {
            Self::Base(v) => Mle::Ref(MleRef::Base(v)),
            Self::Extension(v) => Mle::Ref(MleRef::Extension(v)),
            Self::BasePacked(pb) => Mle::Ref(MleRef::Base(PFPacking::<EF>::unpack_slice(pb))),
            Self::ExtensionPacked(ep) => Mle::Owned(MleOwned::Extension(unpack_extension(ep))),
        }
    }

    pub fn is_packed(&self) -> bool {
        self.by_ref().is_packed()
    }

    pub fn n_vars(&self) -> usize {
        self.by_ref().n_vars()
    }

    pub fn halve(mut self) -> Self {
        match &mut self {
            Self::Base(v) => {
                v.truncate(v.len() / 2);
            }
            Self::Extension(v) => {
                v.truncate(v.len() / 2);
            }
            Self::BasePacked(v) => {
                if v.len() == 1 {
                    return self.unpack().by_ref().clone_to_owned().halve();
                }
                v.truncate(v.len() / 2);
            }
            Self::ExtensionPacked(v) => {
                if v.len() == 1 {
                    return self.unpack().by_ref().clone_to_owned().halve();
                }
                v.truncate(v.len() / 2);
            }
        }
        self
    }
}
