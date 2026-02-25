use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolder<'a, NF, EF, ExtraData: AlphaPowers<EF>>
where
    NF: ExtensionField<PF<EF>>,
    EF: ExtensionField<NF>,
{
    pub up: &'a [NF],
    pub down: &'a [NF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EF,
    pub constraint_index: usize,
}

impl<'a, NF, EF, ExtraData: AlphaPowers<EF>> AirBuilder for ConstraintFolder<'a, NF, EF, ExtraData>
where
    NF: ExtensionField<PF<EF>>,
    EF: Field + ExtensionField<NF>,
{
    type F = NF;
    type EF = EF;

    #[inline]
    fn up(&self) -> &[Self::F] {
        self.up
    }

    #[inline]
    fn down(&self) -> &[Self::F] {
        self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: NF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += alpha_power * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: EF) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += alpha_power * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn eval_virtual_column(&mut self, x: Self::EF) {
        self.assert_zero_ef(x);
    }
}
