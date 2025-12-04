use std::collections::BTreeMap;

use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::get_poseidon_24_of_zero;

const POSEIDON_24_CORE_COL_FLAG: ColIndex = 0;
pub const POSEIDON_24_CORE_COL_INPUT_START: ColIndex = 1;
// virtual via GKR
pub const POSEIDON_24_CORE_COL_OUTPUT_START: ColIndex = POSEIDON_24_CORE_COL_INPUT_START + 24;
// intermediate columns ("commited cubes") are not handled here

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon24CorePrecompile;

impl TableT for Poseidon24CorePrecompile {
    fn name(&self) -> &'static str {
        "poseidon24_core"
    }

    fn identifier(&self) -> Table {
        Table::poseidon24_core()
    }

    fn n_columns_f_total(&self) -> usize {
        1 + 24 + 8
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        [
            vec![POSEIDON_24_CORE_COL_FLAG],
            (POSEIDON_24_CORE_COL_INPUT_START..POSEIDON_24_CORE_COL_INPUT_START + 24).collect::<Vec<ColIndex>>(),
        ]
        .concat()
        // (committed cubes are handled elsewhere)
    }

    fn commited_columns_ef(&self) -> Vec<ColIndex> {
        vec![]
    }

    fn normal_lookups_f(&self) -> Vec<LookupIntoMemory> {
        vec![]
    }

    fn normal_lookups_ef(&self) -> Vec<ExtensionFieldLookupIntoMemory> {
        vec![]
    }

    fn vector_lookups(&self) -> Vec<VectorLookupIntoMemory> {
        vec![]
    }

    fn buses(&self) -> Vec<Bus> {
        vec![Bus {
            table: BusTable::Constant(self.identifier()),
            direction: BusDirection::Pull,
            selector: BusSelector::Column(POSEIDON_24_CORE_COL_FLAG),
            data: [
                (POSEIDON_24_CORE_COL_INPUT_START..POSEIDON_24_CORE_COL_INPUT_START + 24).collect::<Vec<ColIndex>>(),
                (POSEIDON_24_CORE_COL_OUTPUT_START..POSEIDON_24_CORE_COL_OUTPUT_START + 8).collect::<Vec<ColIndex>>(),
            ]
            .concat(),
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        [
            vec![F::ZERO],
            vec![F::ZERO; 24],
            get_poseidon_24_of_zero()[16..].to_vec(),
        ]
        .concat()
    }

    fn padding_row_ef(&self) -> Vec<EF> {
        vec![]
    }

    #[inline(always)]
    fn execute(&self, _: F, _: F, _: F, _: usize, _: &mut InstructionContext<'_>) -> Result<(), RunnerError> {
        unreachable!()
    }
}

impl Air for Poseidon24CorePrecompile {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        1 + 24 + 8
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        2
    }
    fn down_column_indexes_f(&self) -> Vec<usize> {
        vec![]
    }
    fn down_column_indexes_ef(&self) -> Vec<usize> {
        vec![]
    }
    fn n_constraints(&self) -> usize {
        1
    }
    fn eval<AB: p3_air::AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let up = builder.up_f();
        let flag = up[POSEIDON_24_CORE_COL_FLAG].clone();
        let mut data = [AB::F::ZERO; 24 + 8];
        data[0..24].clone_from_slice(&up[POSEIDON_24_CORE_COL_INPUT_START..][..24]);
        data[24..32].clone_from_slice(&up[POSEIDON_24_CORE_COL_OUTPUT_START..][..8]);

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            &data,
        ));
    }
}

pub fn add_poseidon_24_core_row(
    traces: &mut BTreeMap<Table, TableTrace>,
    multiplicity: usize,
    input: [F; 24],
    res: [F; 8],
) {
    let trace = traces.get_mut(&Table::poseidon24_core()).unwrap();

    trace.base[POSEIDON_24_CORE_COL_FLAG].push(F::from_usize(multiplicity));
    for (i, value) in input.iter().enumerate() {
        trace.base[POSEIDON_24_CORE_COL_INPUT_START + i].push(*value);
    }
    for (i, value) in res.iter().enumerate() {
        trace.base[POSEIDON_24_CORE_COL_OUTPUT_START + i].push(*value);
    }
}
