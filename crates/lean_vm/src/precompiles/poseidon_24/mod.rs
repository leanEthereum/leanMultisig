use crate::{
    Bus, BusDirection, BusSelector, ColIndex, EF, ExtensionFieldLookupIntoMemory, F,
    LookupIntoMemory, Memory, ModularPrecompile, POSEIDON_24_NULL_HASH_PTR,
    PrecompileExecutionContext, PrecompileTrace, RunnerError, Table, VECTOR_LEN,
    VectorLookupIntoMemory, ZERO_VEC_PTR,
};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::{ToUsize, poseidon24_permute};

pub const POSEIDON_24_COL_INDEX_A: ColIndex = 0;
pub const POSEIDON_24_COL_INDEX_A_BIS: ColIndex = 1;
pub const POSEIDON_24_COL_INDEX_B: ColIndex = 2;
pub const POSEIDON_24_COL_INDEX_RES: ColIndex = 3;
pub const POSEIDON_24_COL_INDEX_INPUT_START: ColIndex = 4;

#[derive(Debug)]
pub struct Poseidon24Precompile;

impl ModularPrecompile for Poseidon24Precompile {
    fn name() -> &'static str {
        "poseidon24"
    }

    fn identifier() -> Table {
        Table::Poseidon24
    }

    fn commited_columns_f() -> Vec<ColIndex> {
        unreachable!()
    }

    fn commited_columns_ef() -> Vec<ColIndex> {
        unreachable!()
    }

    fn simple_lookups() -> &'static [LookupIntoMemory] {
        &[]
    }

    fn ext_field_lookups() -> &'static [ExtensionFieldLookupIntoMemory] {
        &[]
    }

    fn vector_lookups() -> &'static [VectorLookupIntoMemory] {
        &[]
    }

    fn buses() -> Vec<Bus> {
        vec![Bus {
            table: Table::Poseidon24,
            direction: BusDirection::Pull,
            selector: BusSelector::DenseOnes,
            data: vec![
                POSEIDON_24_COL_INDEX_A,
                POSEIDON_24_COL_INDEX_B,
                POSEIDON_24_COL_INDEX_RES,
            ],
        }]
    }

    #[inline(always)]
    fn execute(
        arg_a: F,
        arg_b: F,
        res: F,
        aux: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        ctx: PrecompileExecutionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert_eq!(aux, 0); // no aux for poseidon24

        let arg0 = memory.get_vector(arg_a.to_usize())?;
        let arg1 = memory.get_vector(1 + arg_a.to_usize())?;
        let arg2 = memory.get_vector(arg_b.to_usize())?;

        let mut input = [F::ZERO; VECTOR_LEN * 3];
        input[..VECTOR_LEN].copy_from_slice(&arg0);
        input[VECTOR_LEN..2 * VECTOR_LEN].copy_from_slice(&arg1);
        input[2 * VECTOR_LEN..].copy_from_slice(&arg2);

        let output = match ctx
            .poseidon24_precomputed
            .get(*ctx.n_poseidon24_precomputed_used)
        {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon24_precomputed_used += 1;
                precomputed.1
            }
            _ => {
                let output = poseidon24_permute(input);
                output[2 * VECTOR_LEN..].try_into().unwrap()
            }
        };

        memory.set_vector(res.to_usize(), output)?;

        trace.base[POSEIDON_24_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_24_COL_INDEX_A_BIS].push(arg_a + F::ONE);
        trace.base[POSEIDON_24_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_24_COL_INDEX_RES].push(res);
        for i in 0..24 {
            trace.base[POSEIDON_24_COL_INDEX_INPUT_START + i].push(input[i]);
        }

        Ok(())
    }

    fn padding_row() -> Vec<EF> {
        [
            vec![
                EF::from_usize(ZERO_VEC_PTR),
                EF::from_usize(ZERO_VEC_PTR + 1),
                EF::from_usize(ZERO_VEC_PTR),
                EF::from_usize(POSEIDON_24_NULL_HASH_PTR),
            ],
            vec![EF::ZERO; 24],
        ]
        .concat()
    }
}

impl Air for Poseidon24Precompile {
    type ExtraData = ();
    fn n_columns_f() -> usize {
        4 + 24
    }
    fn n_columns_ef() -> usize {
        0
    }
    fn degree() -> usize {
        unreachable!()
    }
    fn down_column_indexes() -> Vec<usize> {
        unreachable!()
    }
    fn n_constraints() -> usize {
        unreachable!()
    }
    fn eval<AB: p3_air::AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}
