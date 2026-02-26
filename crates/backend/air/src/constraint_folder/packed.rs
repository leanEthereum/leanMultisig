use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolderPackedBase<'a, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub up: &'a [PFPacking<EF>],
    pub down: &'a [PFPacking<EF>],
    pub extra_data: &'a ExtraData,
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> AirBuilder
    for ConstraintFolderPackedBase<'a, EF, ExtraData>
{
    type F = PFPacking<EF>;
    type EF = EFPacking<EF>;

    #[inline]
    fn up(&self) -> &[Self::F] {
        self.up
    }

    #[inline]
    fn down(&self) -> &[Self::F] {
        self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: Self::F) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: Self::EF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += x * alpha_power;
        self.constraint_index += 1;
    }

    #[inline]
    fn eval_virtual_column(&mut self, x: Self::EF) {
        self.assert_zero_ef(x);
    }
}

#[derive(Debug)]
pub struct ConstraintFolderPackedExtension<'a, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub up: &'a [EFPacking<EF>],
    pub down: &'a [EFPacking<EF>],
    pub extra_data: &'a ExtraData,
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> AirBuilder
    for ConstraintFolderPackedExtension<'a, EF, ExtraData>
{
    type F = EFPacking<EF>;
    type EF = EFPacking<EF>;

    #[inline]
    fn up(&self) -> &[Self::F] {
        self.up
    }

    #[inline]
    fn down(&self) -> &[Self::F] {
        self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: Self::F) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += x * alpha_power;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: Self::EF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += x * alpha_power;
        self.constraint_index += 1;
    }

    #[inline]
    fn eval_virtual_column(&mut self, x: Self::EF) {
        self.assert_zero_ef(x);
    }
}
