use p3_air::Air;

pub type ColIndex = usize;
pub type BusIndex = usize;

#[derive(Debug)]
pub struct LookupIntoMemory {
    pub index: ColIndex,
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct ExtensionFieldLookupIntoMemory {
    pub index: ColIndex,
    pub values: ColIndex,
}

#[derive(Debug)]
pub struct VectorLookupIntoMemory {
    pub index: ColIndex,
    pub values: [ColIndex; 8],
}

#[derive(Debug)]
pub enum BusDirection {
    Pull,
    Push,
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub bus_index: BusIndex,
    pub data: Vec<ColIndex>, // only commited columns (for now)
}

pub trait ModularPrecompile: Air {
    fn name(&self) -> &str;
    fn commited_columns(&self) -> &[ColIndex];
    fn simple_lookups(&self) -> &[LookupIntoMemory];
    fn ext_field_lookups(&self) -> &[ExtensionFieldLookupIntoMemory];
    fn vector_lookups(&self) -> &[VectorLookupIntoMemory];
    fn buses(&self) -> &[Bus];
}
