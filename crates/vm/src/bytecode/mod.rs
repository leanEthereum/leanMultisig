use std::{
    collections::BTreeMap,
    fmt,
    fmt::{Display, Formatter},
};

use utils::{build_poseidon16, build_poseidon24, pretty_integer};

use crate::{
    DIMENSION, ExecutionResult, F, MAX_MEMORY_SIZE, Memory, PUBLIC_INPUT_START, RunnerError,
    build_public_memory,
};

pub mod operand;
pub use operand::*;
pub mod hint;
pub use hint::*;
pub mod operation;
pub use operation::*;
pub mod instruction;
pub use instruction::*;

pub type Label = String;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bytecode {
    pub instructions: Vec<Instruction>,
    pub hints: BTreeMap<usize, Vec<Hint>>, // pc -> hints
    pub starting_frame_memory: usize,
    pub ending_pc: usize,
}

impl Bytecode {
    #[must_use]
    pub fn execute(&self, public_input: &[F], private_input: &[F]) -> ExecutionResult {
        let mut std_out = String::new();
        let first = self
            .execute_internal(
                public_input,
                private_input,
                MAX_MEMORY_SIZE / 2,
                false,
                &mut std_out,
            )
            .unwrap_or_else(|err| {
                if !std_out.is_empty() {
                    print!("{std_out}");
                }
                panic!("Error during bytecode execution: {err}");
            });

        self.execute_internal(
            public_input,
            private_input,
            first.no_vec_runtime_memory,
            true,
            &mut String::new(),
        )
        .unwrap()
    }

    pub(crate) fn execute_internal(
        &self,
        public_input: &[F],
        private_input: &[F],
        no_vec_runtime_memory: usize,
        final_execution: bool,
        std_out: &mut String,
    ) -> Result<ExecutionResult, RunnerError> {
        // TODO avoid rebuilding each time
        let (p16, p24) = (build_poseidon16(), build_poseidon24());

        // set public memory
        let mut memory = Memory::new(build_public_memory(public_input));

        let public_memory_size = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
        let mut fp = public_memory_size;

        private_input
            .iter()
            .copied()
            .enumerate()
            .try_for_each(|(i, v)| memory.set(fp + i, v))?;

        fp = (fp + private_input.len()).next_multiple_of(DIMENSION);

        let initial_ap = fp + self.starting_frame_memory;
        let initial_ap_vec =
            (initial_ap + no_vec_runtime_memory).next_multiple_of(DIMENSION) / DIMENSION;

        let (mut pc, mut ap, mut ap_vec) = (0, initial_ap, initial_ap_vec);

        let mut poseidon16_calls = 0;
        let mut poseidon24_calls = 0;
        let mut dot_product_ext_ext_calls = 0;
        let mut dot_product_base_ext_calls = 0;
        let mut cpu_cycles = 0;

        let mut last_checkpoint_cpu_cycles = 0;
        let mut checkpoint_ap = initial_ap;
        let mut checkpoint_ap_vec = ap_vec;

        let mut pcs = Vec::new();
        let mut fps = Vec::new();

        while pc != self.ending_pc {
            if pc >= self.instructions.len() {
                return Err(RunnerError::PCOutOfBounds);
            }

            pcs.push(pc);
            fps.push(fp);

            cpu_cycles += 1;

            // hints (no PC change)
            for hint in self.hints.get(&pc).unwrap_or(&vec![]) {
                hint.execute(
                    &mut memory,
                    fp,
                    &mut ap,
                    &mut ap_vec,
                    std_out,
                    cpu_cycles,
                    &mut last_checkpoint_cpu_cycles,
                    &mut checkpoint_ap,
                    &mut checkpoint_ap_vec,
                )?;
            }

            // instruction
            self.instructions[pc].execute(
                &mut memory,
                &mut fp,
                &mut pc,
                &p16,
                &p24,
                &mut poseidon16_calls,
                &mut poseidon24_calls,
                &mut dot_product_ext_ext_calls,
                &mut dot_product_base_ext_calls,
            )?;
        }

        debug_assert_eq!(pc, self.ending_pc);
        pcs.push(pc);
        fps.push(fp);

        if final_execution {
            if !std_out.is_empty() {
                print!("{std_out}");
            }
            print_report(
                self,
                public_input.len(),
                private_input.len(),
                cpu_cycles,
                &memory,
                initial_ap_vec,
                ap_vec,
                poseidon16_calls,
                poseidon24_calls,
                dot_product_ext_ext_calls,
                dot_product_base_ext_calls,
            );
        }

        Ok(ExecutionResult {
            no_vec_runtime_memory: ap - initial_ap,
            public_memory_size,
            memory,
            pcs,
            fps,
        })
    }
}

impl Display for Bytecode {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        for (pc, instruction) in self.instructions.iter().enumerate() {
            if let Some(hints) = self.hints.get(&pc) {
                for hint in hints {
                    writeln!(f, "hint: {hint}")?;
                }
            }
            writeln!(f, "{pc:>4}: {instruction}")?;
        }
        Ok(())
    }
}

fn print_report(
    bc: &Bytecode,
    public_in_len: usize,
    private_in_len: usize,
    cycles: usize,
    memory: &Memory,
    initial_ap_vec: usize,
    ap_vec: usize,
    p16_calls: usize,
    p24_calls: usize,
    dp_ext_ext_calls: usize,
    dp_base_ext_calls: usize,
) {
    println!("\nBytecode size: {}", pretty_integer(bc.instructions.len()));
    println!("Public input size: {}", pretty_integer(public_in_len));
    println!("Private input size: {}", pretty_integer(private_in_len));
    println!("Executed {} instructions", pretty_integer(cycles));

    let runtime_mem = memory.0.len() - (PUBLIC_INPUT_START + public_in_len);
    println!(
        "Runtime memory: {} ({:.2}% vec)",
        pretty_integer(runtime_mem),
        (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_mem as f64 * 100.0
    );

    let total_poseidon = p16_calls + p24_calls;
    if total_poseidon > 0 {
        println!(
            "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
            pretty_integer(p16_calls),
            pretty_integer(p24_calls),
            cycles / total_poseidon
        );
    }
    if dp_ext_ext_calls > 0 {
        println!(
            "DotProductExtExt calls: {}",
            pretty_integer(dp_ext_ext_calls)
        );
    }
    if dp_base_ext_calls > 0 {
        println!(
            "DotProductBaseExt calls: {}",
            pretty_integer(dp_base_ext_calls)
        );
    }

    let used_cells = memory
        .0
        .iter()
        .skip(PUBLIC_INPUT_START + public_in_len)
        .filter(|&&x| x.is_some())
        .count();
    println!(
        "Memory usage: {:.1}%",
        used_cells as f64 / runtime_mem as f64 * 100.0
    );
}
