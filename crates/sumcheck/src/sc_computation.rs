use std::any::TypeId;

use p3_air::Air;
use p3_field::{ExtensionField, Field};
use p3_matrix::dense::RowMajorMatrixView;
use utils::{
    ConstraintFolder, ConstraintFolderPackedBase, ConstraintFolderPackedExtension, EFPacking, PF,
    PFPacking,
};

pub trait SumcheckComputation<NF, EF>: Sync {
    fn degree(&self) -> usize;
    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF;
}

impl<NF, EF, A> SumcheckComputation<NF, EF> for A
where
    NF: ExtensionField<PF<EF>>,
    EF: ExtensionField<NF> + ExtensionField<PF<EF>>,
    A: for<'a> Air<ConstraintFolder<'a, NF, EF>>,
{
    fn eval(&self, point: &[NF], alpha_powers: &[EF]) -> EF {
        if self.structured() {
            assert_eq!(point.len(), A::width(self) * 2);
        } else {
            assert_eq!(point.len(), A::width(self));
        }
        let mut folder = ConstraintFolder {
            main: RowMajorMatrixView::new(point, A::width(self)),
            alpha_powers,
            accumulator: EF::ZERO,
            constraint_index: 0,
        };
        self.eval(&mut folder);
        folder.accumulator
    }
    fn degree(&self) -> usize {
        self.degree()
    }
}

pub trait SumcheckComputationPacked<EF>: Sync
where
    EF: ExtensionField<PF<EF>>,
{
    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF>;
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF>;
    fn degree(&self) -> usize;
}

impl<EF: Field, A> SumcheckComputationPacked<EF> for A
where
    EF: ExtensionField<PF<EF>>,
    A: for<'a> Air<ConstraintFolderPackedBase<'a, EF>>
        + for<'a> Air<ConstraintFolderPackedExtension<'a, EF>>,
{
    fn eval_packed_base(&self, point: &[PFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        if self.structured() {
            assert_eq!(point.len(), A::width(self) * 2);
        } else {
            assert_eq!(point.len(), A::width(self));
        }
        let mut folder = ConstraintFolderPackedBase {
            main: RowMajorMatrixView::new(point, A::width(self)),
            alpha_powers,
            accumulator: Default::default(),
            constraint_index: 0,
        };
        self.eval(&mut folder);

        folder.accumulator
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], alpha_powers: &[EF]) -> EFPacking<EF> {
        if self.structured() {
            assert_eq!(point.len(), A::width(self) * 2);
        } else {
            assert_eq!(point.len(), A::width(self));
        }
        let mut folder = ConstraintFolderPackedExtension {
            main: RowMajorMatrixView::new(point, A::width(self)),
            alpha_powers,
            accumulator: Default::default(),
            constraint_index: 0,
        };
        self.eval(&mut folder);

        folder.accumulator
    }

    fn degree(&self) -> usize {
        self.degree()
    }
}

#[derive(Debug)]
pub struct ProductComputation;

impl<IF: ExtensionField<PF<EF>>, EF: ExtensionField<IF>> SumcheckComputation<IF, EF>
    for ProductComputation
{
    fn eval(&self, point: &[IF], _: &[EF]) -> EF {
        if TypeId::of::<IF>() == TypeId::of::<EF>() {
            let point = unsafe { std::mem::transmute::<&[IF], &[EF]>(point) };
            unsafe { *point.get_unchecked(0) * *point.get_unchecked(1) }
        } else {
            todo!("There would be embedding overhead ...?")
        }
    }
    fn degree(&self) -> usize {
        2
    }
}

impl<EF: ExtensionField<PF<EF>>> SumcheckComputationPacked<EF> for ProductComputation {
    fn eval_packed_base(&self, _: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        unreachable!()
    }
    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        unsafe { *point.get_unchecked(0) * *point.get_unchecked(1) }
    }
    fn degree(&self) -> usize {
        2
    }
}
