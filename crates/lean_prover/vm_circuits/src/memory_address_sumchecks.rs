use multilinear_toolkit::prelude::{
    EFPacking, PF, PFPacking, SumcheckComputation, SumcheckComputationPacked,
};
use p3_field::PrimeCharacteristicRing;
use p3_field::{ExtensionField, Field};

#[derive(Debug)]
pub struct SumcheckMemAddressC {}

impl<NF: Field, EF: ExtensionField<NF>> SumcheckComputation<NF, EF> for SumcheckMemAddressC {
    fn degree(&self) -> usize {
        2
    }
    fn eval(&self, point: &[NF], _: &[EF]) -> EF {
        // TODO avoid embedding
        EF::from(sumcheck_compute_mem_address_c(point))
    }
}

impl<EF: ExtensionField<PF<EF>>> SumcheckComputationPacked<EF> for SumcheckMemAddressC {
    fn degree(&self) -> usize {
        2
    }

    fn eval_packed_base(&self, point: &[PFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        // TODO avoid embedding
        EFPacking::<EF>::from(sumcheck_compute_mem_address_c(point))
    }

    fn eval_packed_extension(&self, point: &[EFPacking<EF>], _: &[EF]) -> EFPacking<EF> {
        sumcheck_compute_mem_address_c(point)
    }
}

fn sumcheck_compute_mem_address_c<A: PrimeCharacteristicRing + Copy>(point: &[A]) -> A {
    // addr_C = (1 - flag_C)(fp + operand_C) + deref(value_A + operand_C)
    debug_assert_eq!(point.len(), 5);

    let flag_c = point[0];
    let fp = point[1];
    let operand_c = point[2];
    let deref = point[3];
    let value_a = point[4];

    (A::ONE - flag_c) * (fp + operand_c) + deref * (value_a + operand_c)
}
