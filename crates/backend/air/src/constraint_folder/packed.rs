use crate::*;
use field::*;
use poly::*;

#[derive(Debug)]
pub struct ConstraintFolderPacked<'a, IF, EF: ExtensionField<PF<EF>>, ExtraData: AlphaPowers<EF>> {
    pub up: &'a [IF],
    pub down: &'a [IF],
    pub extra_data: &'a ExtraData,
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
    pub skip_low: bool,
    pub accumulator_low: EFPacking<EF>,
    pub cached_state: Option<Vec<IF>>,
    pub low_ci_count: usize,
}

impl<'a, IF, EF, ExtraData> ConstraintFolderPacked<'a, IF, EF, ExtraData>
where
    EF: ExtensionField<PF<EF>>,
    EFPacking<EF>: PrimeCharacteristicRing,
    ExtraData: AlphaPowers<EF>,
{
    pub fn new(up: &'a [IF], down: &'a [IF], extra_data: &'a ExtraData) -> Self {
        Self {
            up,
            down,
            extra_data,
            accumulator: EFPacking::<EF>::ZERO,
            constraint_index: 0,
            skip_low: false,
            accumulator_low: EFPacking::<EF>::ZERO,
            cached_state: None,
            low_ci_count: 0,
        }
    }
}

impl<'a, IF, EF, ExtraData> AirBuilder for ConstraintFolderPacked<'a, IF, EF, ExtraData>
where
    IF: Algebra<PFPacking<EF>> + 'static,
    EF: Field + ExtensionField<PF<EF>>,
    EFPacking<EF>: PrimeCharacteristicRing + Mul<IF, Output = EFPacking<EF>> + Add<IF, Output = EFPacking<EF>>,
    ExtraData: AlphaPowers<EF>,
{
    type F = PFPacking<EF>;
    type IF = IF;
    type EF = EFPacking<EF>;

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
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: EFPacking<EF>) {
        let alpha_power = self.extra_data.alpha_powers()[self.constraint_index];
        self.accumulator += EFPacking::<EF>::from(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn eval_virtual_column(&mut self, x: Self::EF) {
        self.assert_zero_ef(x);
    }
}
