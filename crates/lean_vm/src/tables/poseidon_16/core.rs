use std::collections::BTreeMap;

use crate::*;
use multilinear_toolkit::prelude::*;
use p3_air::Air;
use utils::get_poseidon_16_of_zero;

const POSEIDON_16_CORE_COL_FLAG: ColIndex = 0;
pub const POSEIDON_16_CORE_COL_COMPRESSION: ColIndex = 1;
pub const POSEIDON_16_CORE_COL_INPUT_START: ColIndex = 2;
// virtual via GKR
pub const POSEIDON_16_CORE_COL_OUTPUT_START: ColIndex = POSEIDON_16_CORE_COL_INPUT_START + 16;
// intermediate columns ("commited cubes") are not handled here

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Poseidon16CorePrecompile;

impl TableT for Poseidon16CorePrecompile {
    fn name(&self) -> &'static str {
        "poseidon16_core"
    }

    fn identifier(&self) -> Table {
        Table::poseidon16_core()
    }

    fn n_columns_f_total(&self) -> usize {
        2 + 16 * 2
    }

    fn commited_columns_f(&self) -> Vec<ColIndex> {
        [
            vec![POSEIDON_16_CORE_COL_FLAG, POSEIDON_16_CORE_COL_COMPRESSION],
            (POSEIDON_16_CORE_COL_INPUT_START..POSEIDON_16_CORE_COL_INPUT_START + 16).collect::<Vec<ColIndex>>(),
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
            selector: BusSelector::Column(POSEIDON_16_CORE_COL_FLAG),
            data: [
                vec![POSEIDON_16_CORE_COL_COMPRESSION],
                (POSEIDON_16_CORE_COL_INPUT_START..POSEIDON_16_CORE_COL_INPUT_START + 16).collect::<Vec<ColIndex>>(),
                (POSEIDON_16_CORE_COL_OUTPUT_START..POSEIDON_16_CORE_COL_OUTPUT_START + 16).collect::<Vec<ColIndex>>(),
            ]
            .concat(),
        }]
    }

    fn padding_row_f(&self) -> Vec<F> {
        let mut poseidon_of_zero = *get_poseidon_16_of_zero();
        if POSEIDON_16_DEFAULT_COMPRESSION {
            poseidon_of_zero[8..].fill(F::ZERO);
        }
        [
            vec![F::ZERO, F::from_bool(POSEIDON_16_DEFAULT_COMPRESSION)],
            vec![F::ZERO; 16],
            poseidon_of_zero.to_vec(),
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

impl Air for Poseidon16CorePrecompile {
    type ExtraData = ExtraDataForBuses<EF>;
    fn n_columns_f_air(&self) -> usize {
        2 + 16 * 2
    }
    fn n_columns_ef_air(&self) -> usize {
        0
    }
    fn degree(&self) -> usize {
        1
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
        let flag = up[POSEIDON_16_CORE_COL_FLAG].clone();
        let mut data = [AB::F::ZERO; 1 + 2 * 16];
        data[0] = up[POSEIDON_16_CORE_COL_COMPRESSION].clone();
        data[1..17].clone_from_slice(&up[POSEIDON_16_CORE_COL_INPUT_START..][..16]);
        data[17..33].clone_from_slice(&up[POSEIDON_16_CORE_COL_OUTPUT_START..][..16]);

        builder.eval_virtual_column(eval_virtual_bus_column::<AB, EF>(
            extra_data,
            AB::F::from_usize(self.identifier().index()),
            flag.clone(),
            &data,
        ));
    }
}

pub fn add_poseidon16_core_row(
    traces: &mut BTreeMap<Table, TableTrace>,
    multiplicity: usize,
    input: [F; 16],
    res_a: [F; 8],
    res_b: [F; 8],
    is_compression: bool,
) {
    let trace = traces.get_mut(&Table::poseidon16_core()).unwrap();

    trace.base[POSEIDON_16_CORE_COL_FLAG].push(F::from_usize(multiplicity));
    trace.base[POSEIDON_16_CORE_COL_COMPRESSION].push(F::from_bool(is_compression));
    for (i, value) in input.iter().enumerate() {
        trace.base[POSEIDON_16_CORE_COL_INPUT_START + i].push(*value);
    }
    for (i, value) in res_a.iter().enumerate() {
        trace.base[POSEIDON_16_CORE_COL_OUTPUT_START + i].push(*value);
    }
    for (i, value) in res_b.iter().enumerate() {
        trace.base[POSEIDON_16_CORE_COL_OUTPUT_START + 8 + i].push(*value);
    }
}
