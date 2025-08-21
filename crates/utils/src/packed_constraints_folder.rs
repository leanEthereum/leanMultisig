use crate::EFPacking;
use crate::PF;
use crate::PFPacking;
use p3_air::AirBuilder;
use p3_field::ExtensionField;
use p3_matrix::dense::RowMajorMatrixView;

#[derive(Debug)]
pub struct ConstraintFolderPackedBase<'a, EF: ExtensionField<PF<EF>>> {
    pub main: RowMajorMatrixView<'a, PFPacking<EF>>,
    pub alpha_powers: &'a [EF],
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>> AirBuilder for ConstraintFolderPackedBase<'a, EF> {
    type F = PF<EF>;
    type I = PF<EF>;
    type Expr = PFPacking<EF>;
    type Var = PFPacking<EF>;
    type M = RowMajorMatrixView<'a, PFPacking<EF>>;

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

    /// Returns an expression indicating rows where transition constraints should be checked.
    ///
    /// # Panics
    /// This function panics if `size` is not `2`.
    #[inline]
    fn is_transition_window(&self, _: usize) -> Self::Expr {
        unreachable!()
    }

    #[inline]
    fn assert_zero<I: Into<Self::Expr>>(&mut self, x: I) {
        let alpha_power = self.alpha_powers[self.constraint_index];
        let x: PFPacking<EF> = x.into();
        self.accumulator += Into::<EFPacking<EF>>::into(alpha_power) * x;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, _array: [I; N]) {
        unreachable!();
        // let expr_array = array.map(Into::into);
        // self.accumulator += EFPacking::<EF>::from_basis_coefficients_fn(|i| {
        //     let alpha_powers = &self.decomposed_alpha_powers[i]
        //         [self.constraint_index..(self.constraint_index + N)];
        //     PFPacking::<EF>::packed_linear_combination::<N>(alpha_powers, &expr_array)
        // });
        // self.constraint_index += N;
    }
}

#[derive(Debug)]
pub struct ConstraintFolderPackedExtension<'a, EF: ExtensionField<PF<EF>>> {
    pub main: RowMajorMatrixView<'a, EFPacking<EF>>,
    pub alpha_powers: &'a [EF],
    pub accumulator: EFPacking<EF>,
    pub constraint_index: usize,
}

impl<'a, EF: ExtensionField<PF<EF>>> AirBuilder for ConstraintFolderPackedExtension<'a, EF> {
    type F = PF<EF>;
    type I = PFPacking<EF>;
    type Expr = EFPacking<EF>;
    type Var = EFPacking<EF>;
    type M = RowMajorMatrixView<'a, EFPacking<EF>>;

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
        let alpha_power = self.alpha_powers[self.constraint_index];
        let x: EFPacking<EF> = x.into();
        self.accumulator += x * alpha_power;
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zeros<const N: usize, I: Into<Self::Expr>>(&mut self, _array: [I; N]) {
        unreachable!();
    }
}
