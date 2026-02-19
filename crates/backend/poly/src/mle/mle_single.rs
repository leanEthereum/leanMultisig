use crate::*;
use field::ExtensionField;

#[derive(Debug)]
pub enum Mle<'a, EF: ExtensionField<PF<EF>>> {
    Owned(MleOwned<EF>),
    Ref(MleRef<'a, EF>),
}

impl<EF: ExtensionField<PF<EF>>> Clone for Mle<'_, EF> {
    fn clone(&self) -> Self {
        match self {
            Self::Owned(o) => Self::Owned(o.clone()),
            Self::Ref(r) => Self::Ref(r.soft_clone()),
        }
    }
}
impl<EF: ExtensionField<PF<EF>>> From<MleOwned<EF>> for Mle<'_, EF> {
    fn from(value: MleOwned<EF>) -> Self {
        Self::Owned(value)
    }
}

impl<'a, EF: ExtensionField<PF<EF>>> From<MleRef<'a, EF>> for Mle<'a, EF> {
    fn from(value: MleRef<'a, EF>) -> Self {
        Self::Ref(value)
    }
}

impl<'a, EF: ExtensionField<PF<EF>>> Mle<'a, EF> {
    pub fn by_ref(&'a self) -> MleRef<'a, EF> {
        match self {
            Self::Owned(owned) => owned.by_ref(),
            Self::Ref(r) => r.soft_clone(),
        }
    }

    pub fn as_owned_mut(&mut self) -> Option<&mut MleOwned<EF>> {
        match self {
            Self::Owned(o) => Some(o),
            _ => None,
        }
    }

    pub fn as_owned(self) -> Option<MleOwned<EF>> {
        match self {
            Self::Owned(o) => Some(o),
            _ => None,
        }
    }

    pub fn evaluate(&self, point: &MultilinearPoint<EF>) -> EF {
        self.by_ref().evaluate(point)
    }

    pub fn pack(&'a self) -> Self {
        match self {
            Self::Owned(poly) => poly.pack(),
            Self::Ref(poly) => poly.pack(),
        }
    }

    pub fn unpack(&'a self) -> Self {
        match self {
            Self::Owned(poly) => poly.unpack(),
            Self::Ref(poly) => poly.unpack(),
        }
    }

    pub fn is_packed(&self) -> bool {
        self.by_ref().is_packed()
    }

    pub fn n_vars(&self) -> usize {
        self.by_ref().n_vars()
    }

    pub fn as_owned_or_clone(self) -> MleOwned<EF> {
        match self {
            Self::Owned(o) => o,
            Self::Ref(r) => r.clone_to_owned(),
        }
    }
}
