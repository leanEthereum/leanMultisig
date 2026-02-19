use crate::*;
use field::ExtensionField;

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

impl<'a, EF: ExtensionField<PF<EF>>> MleGroup<'a, EF> {
    pub fn by_ref(&'a self) -> MleGroupRef<'a, EF> {
        match self {
            Self::Owned(owned) => owned.by_ref(),
            Self::Ref(r) => r.soft_clone(),
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

    pub fn as_owned(self) -> Option<MleGroupOwned<EF>> {
        match self {
            Self::Owned(owned) => Some(owned),
            Self::Ref(_) => None,
        }
    }

    pub fn as_owned_mut(&mut self) -> Option<&mut MleGroupOwned<EF>> {
        match self {
            Self::Owned(owned) => Some(owned),
            Self::Ref(_) => None,
        }
    }

    pub fn is_packed(&self) -> bool {
        match self {
            Self::Owned(owned) => owned.is_packed(),
            Self::Ref(r) => r.is_packed(),
        }
    }

    pub fn is_extension(&self) -> bool {
        match self {
            Self::Owned(o) => o.is_extension(),
            Self::Ref(r) => r.is_extension(),
        }
    }

    pub fn as_owned_or_clone(self) -> MleGroupOwned<EF> {
        match self {
            Self::Owned(owned) => owned,
            Self::Ref(r) => r.clone_to_owned(),
        }
    }
}
