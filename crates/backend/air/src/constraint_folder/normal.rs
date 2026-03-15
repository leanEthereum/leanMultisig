use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolder<'a, IF, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub up: &'a [IF],
    pub down: &'a [IF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EF,
    pub constraint_index: usize,
}

impl<'a, IF, EF, ExtraData> AirBuilder for ConstraintFolder<'a, IF, EF, ExtraData>
where
    IF: Algebra<PF<EF>> + 'static,
    EF: Field + ExtensionField<PF<EF>> + Mul<IF, Output = EF> + Add<IF, Output = EF>,
    ExtraData: AlphaPowers<EF>,
{
    type F = PF<EF>;
    type IF = IF;
    type EF = EF;

    #[inline]
    fn up(&self) -> &[Self::IF] {
        self.up
    }

    #[inline]
    fn down(&self) -> &[Self::IF] {
        self.down
    }

    #[inline]
    fn assert_zero(&mut self, x: IF) {
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
