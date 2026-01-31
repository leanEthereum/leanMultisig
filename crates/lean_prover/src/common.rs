use crate::*;
use lean_vm::*;

pub(crate) fn fold_bytecode(bytecode: &Bytecode, folding_challenges: &MultilinearPoint<EF>) -> Vec<EF> {
    let encoded_bytecode = padd_with_zero_to_next_power_of_two(
        &bytecode
            .instructions
            .par_iter()
            .flat_map(|i| padd_with_zero_to_next_power_of_two(&field_representation(i)))
            .collect::<Vec<_>>(),
    );
    fold_multilinear_chunks(&encoded_bytecode, folding_challenges)
}

fn split_at(stmt: &MultiEvaluation<EF>, start: usize, end: usize) -> Vec<MultiEvaluation<EF>> {
    vec![MultiEvaluation::new(
        stmt.point.clone(),
        stmt.values[start..end].to_vec(),
    )]
}
