use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};

use crate::{
    air::constant::{N_EXEC_AIR_COLUMNS, N_INSTRUCTION_COLUMNS},
    bytecode::{Bytecode, program::ExecutionResult},
    constant::{F, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR},
    context::run_context::RunContext,
    errors::vm::VirtualMachineError,
    memory::address::MemoryAddress,
    poseidon2::{build_poseidon16, build_poseidon24},
    witness::{
        Witness,
        dot_product::WitnessDotProduct,
        multilinear_eval::WitnessMultilinearEval,
        poseidon::{WitnessPoseidon16, WitnessPoseidon24},
    },
};

/// Represents the complete trace of a program's execution, including precompile data.
#[derive(Debug)]
pub struct ExecutionTrace {
    /// The main CPU trace columns.
    pub full_trace: Vec<Vec<F>>,
    /// The actual number of Poseidon16 operations executed.
    pub n_poseidons_16: usize,
    /// The actual number of Poseidon24 operations executed.
    pub n_poseidons_24: usize,
    /// Padded witness data for all Poseidon16 operations.
    pub poseidons_16: Vec<WitnessPoseidon16>,
    /// Padded witness data for all Poseidon24 operations.
    pub poseidons_24: Vec<WitnessPoseidon24>,
    /// Witness data for all dot product operations.
    pub dot_products: Vec<WitnessDotProduct>,
    /// Witness data for all multilinear evaluation operations.
    pub vm_multilinear_evals: Vec<WitnessMultilinearEval>,
    /// The size of the public memory region.
    pub public_memory_size: usize,
    /// The final, flattened state of the VM's memory.
    pub memory: Vec<F>,
}

impl ExecutionTrace {
    /// Creates a new `ExecutionTrace` by processing the results of a VM run.
    ///
    /// This function builds the entire trace, including the main CPU trace and all
    /// precompile witness data, based on the provided bytecode and execution result.
    pub fn new(
        bytecode: &Bytecode,
        execution_result: &ExecutionResult,
    ) -> Result<Self, VirtualMachineError> {
        // --- Initialization ---
        // Ensure the pc and fp traces from the execution result have the same length.
        assert_eq!(execution_result.pcs.len(), execution_result.fps.len());
        // Get the total number of execution cycles.
        let n_cycles = execution_result.pcs.len();
        // Determine the padded length for the trace, which must be a power of two.
        let trace_len = n_cycles.next_power_of_two();

        // Initialize the main trace columns with zeros, sized to the padded length.
        let mut trace = (0..N_INSTRUCTION_COLUMNS + N_EXEC_AIR_COLUMNS)
            .map(|_| vec![F::ZERO; trace_len])
            .collect::<Vec<Vec<F>>>();

        // Initialize vectors to store the witnesses for each precompile type.
        let mut poseidons_16 = Vec::new();
        let mut poseidons_24 = Vec::new();
        let mut dot_products = Vec::new();
        let mut vm_multilinear_evals = Vec::new();

        // --- Trace Generation Loop ---
        // Iterate over each cycle of the execution to build the trace row by row.
        for (cycle, (&pc, &fp)) in execution_result
            .pcs
            .iter()
            .zip(&execution_result.fps)
            .enumerate()
        {
            // Get the instruction for the current cycle from the bytecode.
            let instruction = &bytecode.instructions[pc.offset];
            // Convert the instruction into its raw field representation for the trace.
            let field_repr = instruction.field_representation();

            // Populate the instruction-specific columns of the trace for the current cycle.
            for (j, &field) in field_repr.iter().enumerate() {
                trace[j][cycle] = field;
            }

            // --- Populate Memory and Register Columns ---
            // Create a temporary RunContext for this cycle to resolve memory addresses and values.
            let run_context = RunContext {
                pc,
                fp,
                ..Default::default()
            };
            let memory_manager = &execution_result.memory_manager;

            // TODO: check how to populate in a clean way
            //
            // // Calculate addresses and fetch values for the three main operands (a, b, c).
            // let (addr_a, value_a) = run_context.get_a(instruction, memory_manager)?;
            // let (addr_b, value_b) = run_context.get_b(instruction, memory_manager)?;
            // let (addr_c, value_c) = run_context.get_c(instruction, memory_manager)?;

            // // Populate the memory and register columns in the trace for the current cycle.
            // trace[COL_INDEX_MEM_VALUE_A][cycle] = value_a.try_into().unwrap_or_default();
            // trace[COL_INDEX_MEM_VALUE_B][cycle] = value_b.try_into().unwrap_or_default();
            // trace[COL_INDEX_MEM_VALUE_C][cycle] = value_c.try_into().unwrap_or_default();
            // trace[COL_INDEX_PC][cycle] = F::from_usize(pc.offset);
            // trace[COL_INDEX_FP][cycle] = F::from_usize(fp.offset);
            // trace[COL_INDEX_MEM_ADDRESS_A][cycle] = F::from_usize(addr_a.offset);
            // trace[COL_INDEX_MEM_ADDRESS_B][cycle] = F::from_usize(addr_b.offset);
            // trace[COL_INDEX_MEM_ADDRESS_C][cycle] = F::from_usize(addr_c.offset);

            // --- Generate Precompile Witnesses ---
            // If the current instruction is a precompile, generate its witness.
            if let Some(witness) =
                instruction.generate_witness(cycle, &run_context, memory_manager)?
            {
                // Match on the witness type and add it to the corresponding vector.
                match witness {
                    Witness::Poseidon16(w) => poseidons_16.push(w),
                    Witness::Poseidon24(w) => poseidons_24.push(w),
                    Witness::DotProduct(w) => dot_products.push(w),
                    Witness::MultilinearEval(w) => vm_multilinear_evals.push(w),
                }
            }
        }

        // --- Padding ---
        // Pad the main trace by repeating the last row's values to fill the remaining space.
        for t in &mut trace {
            let last_value = t[n_cycles - 1];
            for tt in t.iter_mut().take(trace_len).skip(n_cycles) {
                *tt = last_value;
            }
        }

        // Flatten the final memory state into a single vector, replacing uninitialized cells with zero.
        let mut memory: Vec<F> = execution_result
            .memory_manager
            .memory
            .data
            .par_iter()
            .flatten()
            .map(|cell| {
                cell.value()
                    .and_then(|val| val.try_into().ok())
                    .unwrap_or(F::ZERO)
            })
            .collect();

        // Resize memory to be a multiple of the public memory size, padding with zeros if necessary.
        memory.resize(
            memory
                .len()
                .next_multiple_of(execution_result.public_memory_size),
            F::ZERO,
        );

        // Get the actual number of Poseidon operations before padding.
        let n_poseidons_16 = poseidons_16.len();
        let n_poseidons_24 = poseidons_24.len();

        // Pad the Poseidon witness vectors to the next power of two for the proof system.
        let empty_poseidon16_output = build_poseidon16().permute([F::ZERO; 16]);
        poseidons_16.resize_with(n_poseidons_16.next_power_of_two(), || WitnessPoseidon16 {
            cycle: None,
            addr_input_a: MemoryAddress::default(),
            addr_input_b: MemoryAddress::default(),
            addr_output: POSEIDON_16_NULL_HASH_PTR,
            input: [F::ZERO; 16],
            output: empty_poseidon16_output,
        });

        let empty_poseidon24_output = build_poseidon24().permute([F::ZERO; 24])[16..24]
            .try_into()
            .unwrap();
        poseidons_24.resize_with(n_poseidons_24.next_power_of_two(), || WitnessPoseidon24 {
            cycle: None,
            addr_input_a: MemoryAddress::default(),
            addr_input_b: MemoryAddress::default(),
            addr_output: POSEIDON_24_NULL_HASH_PTR,
            input: [F::ZERO; 24],
            output: empty_poseidon24_output,
        });

        // Construct and return the final ExecutionTrace struct.
        Ok(Self {
            full_trace: trace,
            n_poseidons_16,
            n_poseidons_24,
            poseidons_16,
            poseidons_24,
            dot_products,
            vm_multilinear_evals,
            public_memory_size: execution_result.public_memory_size,
            memory,
        })
    }
}
