use p3_air::AirBuilder;
use p3_field::{ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrixView;

use crate::PF;

#[derive(Debug)]
pub struct ConstraintFolder<'a, NF, EF>
where
    NF: ExtensionField<PF<EF>>,
    EF: ExtensionField<NF>,
{
    pub main: RowMajorMatrixView<'a, NF>,
    pub alpha_powers: &'a [EF],
    pub accumulator: EF,
    pub constraint_index: usize,
}

impl<'a, NF, EF> AirBuilder for ConstraintFolder<'a, NF, EF>
where
    NF: ExtensionField<PF<EF>>,
    EF: Field + ExtensionField<NF>,
{
    type F = PF<EF>;
    type I = Self::F;
    type Expr = NF;
    type Var = NF;
    type M = RowMajorMatrixView<'a, NF>;

    #[inline]
    fn main(&self) -> Self::M {
        self.main
    }

    #[inline]
    fn is_first_row(&self) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn is_last_row(&self) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let x: NF = x.into();
        let alpha_power = self.alpha_powers[self.constraint_index];
        self.accumulator += alpha_power * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, _: [I; N]) {
        unreachable!()
    }
}
