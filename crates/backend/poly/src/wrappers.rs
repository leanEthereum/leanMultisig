use field::{ExtensionField, Field, PrimeCharacteristicRing};

pub type PF<F> = <F as PrimeCharacteristicRing>::PrimeSubfield;
pub type FPacking<F> = <F as Field>::Packing;
pub type PFPacking<F> = <PF<F> as Field>::Packing;
pub type EFPacking<EF> = <EF as ExtensionField<PF<EF>>>::ExtensionPacking;
