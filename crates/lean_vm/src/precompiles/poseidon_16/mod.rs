use crate::{
    Bus, BusDirection, BusSelector, ColIndex, EF, ExtensionFieldLookupIntoMemory, F,
    LookupIntoMemory, Memory, ModularPrecompile, POSEIDON_16_NULL_HASH_PTR,
    PrecompileExecutionContext, PrecompileTrace, RunnerError, Table, VECTOR_LEN,
    VectorLookupIntoMemory, ZERO_VEC_PTR,
};
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::{ToUsize, poseidon16_permute};

pub const POSEIDON_16_DEFAULT_COMPRESSION: bool = true;

pub const POSEIDON_16_COL_INDEX_A: ColIndex = 0;
pub const POSEIDON_16_COL_INDEX_B: ColIndex = 1;
pub const POSEIDON_16_COL_INDEX_RES: ColIndex = 2;
pub const POSEIDON_16_COL_INDEX_RES_BIS: ColIndex = 3; // = if compressed { 0 } else { POSEIDON_16_COL_INDEX_RES + 1 }
pub const POSEIDON_16_COL_INDEX_COMPRESSION: ColIndex = 4;
pub const POSEIDON_16_COL_INDEX_INPUT_START: ColIndex = 5;

#[derive(Debug)]
pub struct Poseidon16Precompile;

impl ModularPrecompile for Poseidon16Precompile {
    fn name() -> &'static str {
        "poseidon16"
    }

    fn identifier() -> Table {
        Table::Poseidon16
    }

    fn commited_columns_f() -> Vec<ColIndex> {
        unreachable!()
    }

    fn commited_columns_ef() -> Vec<ColIndex> {
        unreachable!()
    }

     fn normal_lookups_f() -> Vec<LookupIntoMemory> {
        unreachable!()
    }

    fn normal_lookups_ef() -> Vec<ExtensionFieldLookupIntoMemory> {
        unreachable!()
    }

    fn vector_lookups() -> Vec<VectorLookupIntoMemory> {
         unreachable!()
    }

    fn buses() -> Vec<Bus> {
        vec![Bus {
            table: Table::Poseidon16,
            direction: BusDirection::Pull,
            selector: BusSelector::DenseOnes,
            data: vec![
                POSEIDON_16_COL_INDEX_A,
                POSEIDON_16_COL_INDEX_B,
                POSEIDON_16_COL_INDEX_RES,
                POSEIDON_16_COL_INDEX_COMPRESSION,
            ],
        }]
    }

    #[inline(always)]
    fn execute(
        arg_a: F,
        arg_b: F,
        res: F,
        is_compression: usize,
        memory: &mut Memory,
        trace: &mut PrecompileTrace,
        ctx: PrecompileExecutionContext<'_>,
    ) -> Result<(), RunnerError> {
        assert!(is_compression == 0 || is_compression == 1);
        let is_compression = is_compression == 1;

        let arg0 = memory.get_vector(arg_a.to_usize())?;
        let arg1 = memory.get_vector(arg_b.to_usize())?;

        let mut input = [F::ZERO; VECTOR_LEN * 2];
        input[..VECTOR_LEN].copy_from_slice(&arg0);
        input[VECTOR_LEN..].copy_from_slice(&arg1);

        let output = match ctx
            .poseidon16_precomputed
            .get(*ctx.n_poseidon16_precomputed_used)
        {
            Some(precomputed) if precomputed.0 == input => {
                *ctx.n_poseidon16_precomputed_used += 1;
                precomputed.1
            }
            _ => poseidon16_permute(input),
        };

        let res0: [F; VECTOR_LEN] = output[..VECTOR_LEN].try_into().unwrap();
        let res1: [F; VECTOR_LEN] = output[VECTOR_LEN..].try_into().unwrap();

        memory.set_vector(res.to_usize(), res0)?;
        if !is_compression {
            memory.set_vector(1 + res.to_usize(), res1)?;
        }

        trace.base[POSEIDON_16_COL_INDEX_A].push(arg_a);
        trace.base[POSEIDON_16_COL_INDEX_B].push(arg_b);
        trace.base[POSEIDON_16_COL_INDEX_RES].push(res);
        trace.base[POSEIDON_16_COL_INDEX_RES_BIS].push(if is_compression {
            F::ZERO
        } else {
            res + F::ONE
        });
        trace.base[POSEIDON_16_COL_INDEX_COMPRESSION].push(F::from_bool(is_compression));
        for i in 0..16 {
            trace.base[POSEIDON_16_COL_INDEX_INPUT_START + i].push(input[i]);
        }
        Ok(())
    }

    fn padding_row() -> Vec<EF> {
        [
            vec![
                EF::from_usize(ZERO_VEC_PTR),
                EF::from_usize(ZERO_VEC_PTR),
                EF::from_usize(POSEIDON_16_NULL_HASH_PTR),
                EF::from_usize(if POSEIDON_16_DEFAULT_COMPRESSION {
                    ZERO_VEC_PTR
                } else {
                    1 + POSEIDON_16_NULL_HASH_PTR
                }),
                EF::from_bool(POSEIDON_16_DEFAULT_COMPRESSION),
            ],
            vec![EF::ZERO; 16],
        ]
        .concat()
    }
}

impl Air for Poseidon16Precompile {
    type ExtraData = ();
    fn n_columns_f() -> usize {
        5 + 16
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
