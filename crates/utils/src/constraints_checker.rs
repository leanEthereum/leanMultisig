use multilinear_toolkit::prelude::*;

/*
Debug purpose
*/

#[derive(Debug)]
pub struct ConstraintChecker<EF: ExtensionField<PF<EF>>> {
    pub up_f: Vec<PF<EF>>,
    pub up_ef: Vec<EF>,
    pub down_f: Vec<PF<EF>>,
    pub down_ef: Vec<EF>,
    pub constraint_index: usize,
    pub errors: Vec<usize>,
}

impl<EF: ExtensionField<PF<EF>>> AirBuilder for ConstraintChecker<EF> {
    type F = PF<EF>;
    type EF = EF;

    #[inline]
    fn up_f(&self) -> &[Self::F] {
        &self.up_f
    }

    #[inline]
    fn up_ef(&self) -> &[Self::EF] {
        &self.up_ef
    }

    #[inline]
    fn down_f(&self) -> &[Self::F] {
        &self.down_f
    }

    #[inline]
    fn down_ef(&self) -> &[Self::EF] {
        &self.down_ef
    }

    #[inline]
    fn assert_zero(&mut self, x: Self::F) {
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    #[inline]
    fn assert_zero_ef(&mut self, x: Self::EF) {
        if !x.is_zero() {
            self.errors.push(self.constraint_index);
        }
        self.constraint_index += 1;
    }

    fn eval_virtual_column(&mut self, _: Self::EF) {
        // do nothing
    }
}
