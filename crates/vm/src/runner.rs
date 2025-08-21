use p3_field::PrimeCharacteristicRing;
use p3_symmetric::Permutation;
use utils::{build_poseidon16, build_poseidon24, pretty_integer};

use crate::{
    DIMENSION, F, MAX_MEMORY_SIZE, Memory, POSEIDON_16_NULL_HASH_PTR, POSEIDON_24_NULL_HASH_PTR,
    PUBLIC_INPUT_START, RunnerError, ZERO_VEC_PTR, bytecode::Bytecode,
};

#[must_use]
pub fn execute_bytecode(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
) -> ExecutionResult {
    let mut std_out = String::new();
    let first_exec = match execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        MAX_MEMORY_SIZE / 2,
        false,
        &mut std_out,
    ) {
        Ok(first_exec) => first_exec,
        Err(err) => {
            if !std_out.is_empty() {
                print!("{std_out}");
            }
            panic!("Error during bytecode execution: {err}");
        }
    };
    execute_bytecode_helper(
        bytecode,
        public_input,
        private_input,
        first_exec.no_vec_runtime_memory,
        true,
        &mut String::new(),
    )
    .unwrap()
}

#[derive(Debug)]
pub struct ExecutionResult {
    pub no_vec_runtime_memory: usize,
    pub public_memory_size: usize,
    pub memory: Memory,
    pub pcs: Vec<usize>,
    pub fps: Vec<usize>,
}

#[must_use]
pub fn build_public_memory(public_input: &[F]) -> Vec<F> {
    // padded to a power of two
    let public_memory_len = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut public_memory = F::zero_vec(public_memory_len);
    public_memory[PUBLIC_INPUT_START..][..public_input.len()].copy_from_slice(public_input);
    for pm in public_memory.iter_mut().take((ZERO_VEC_PTR + 2) * 8) {
        *pm = F::ZERO; // zero vector
    }
    public_memory[POSEIDON_16_NULL_HASH_PTR * 8..(POSEIDON_16_NULL_HASH_PTR + 2) * 8]
        .copy_from_slice(&build_poseidon16().permute([F::ZERO; 16]));
    public_memory[POSEIDON_24_NULL_HASH_PTR * 8..(POSEIDON_24_NULL_HASH_PTR + 1) * 8]
        .copy_from_slice(&build_poseidon24().permute([F::ZERO; 24])[16..]);
    public_memory
}

fn execute_bytecode_helper(
    bytecode: &Bytecode,
    public_input: &[F],
    private_input: &[F],
    no_vec_runtime_memory: usize,
    final_execution: bool,
    std_out: &mut String,
) -> Result<ExecutionResult, RunnerError> {
    let poseidon_16 = build_poseidon16(); // TODO avoid rebuilding each time
    let poseidon_24 = build_poseidon24();

    // set public memory
    let mut memory = Memory::new(build_public_memory(public_input));

    let public_memory_size = (PUBLIC_INPUT_START + public_input.len()).next_power_of_two();
    let mut fp = public_memory_size;

    for (i, value) in private_input.iter().enumerate() {
        memory.set(fp + i, *value)?;
    }
    fp += private_input.len();
    fp = fp.next_multiple_of(DIMENSION);

    let initial_ap = fp + bytecode.starting_frame_memory;
    let initial_ap_vec =
        (initial_ap + no_vec_runtime_memory).next_multiple_of(DIMENSION) / DIMENSION;

    let mut pc = 0;
    let mut ap = initial_ap;
    let mut ap_vec = initial_ap_vec;

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

    while pc != bytecode.ending_pc {
        if pc >= bytecode.instructions.len() {
            return Err(RunnerError::PCOutOfBounds);
        }

        pcs.push(pc);
        fps.push(fp);

        cpu_cycles += 1;

        for hint in bytecode.hints.get(&pc).unwrap_or(&vec![]) {
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

        bytecode.instructions[pc].execute(
            &mut memory,
            &mut fp,
            &mut pc,
            &poseidon_16,
            &poseidon_24,
            &mut poseidon16_calls,
            &mut poseidon24_calls,
            &mut dot_product_ext_ext_calls,
            &mut dot_product_base_ext_calls,
        )?;
    }

    debug_assert_eq!(pc, bytecode.ending_pc);
    pcs.push(pc);
    fps.push(fp);

    if final_execution {
        if !std_out.is_empty() {
            print!("{std_out}");
        }
        let runtime_memory_size = memory.0.len() - (PUBLIC_INPUT_START + public_input.len());
        println!(
            "\nBytecode size: {}",
            pretty_integer(bytecode.instructions.len())
        );
        println!("Public input size: {}", pretty_integer(public_input.len()));
        println!(
            "Private input size: {}",
            pretty_integer(private_input.len())
        );
        println!("Executed {} instructions", pretty_integer(cpu_cycles));
        println!(
            "Runtime memory: {} ({:.2}% vec)",
            pretty_integer(runtime_memory_size),
            (DIMENSION * (ap_vec - initial_ap_vec)) as f64 / runtime_memory_size as f64 * 100.0
        );
        if poseidon16_calls + poseidon24_calls > 0 {
            println!(
                "Poseidon2_16 calls: {}, Poseidon2_24 calls: {} (1 poseidon per {} instructions)",
                pretty_integer(poseidon16_calls),
                pretty_integer(poseidon24_calls),
                cpu_cycles / (poseidon16_calls + poseidon24_calls)
            );
        }
        if dot_product_ext_ext_calls > 0 {
            println!(
                "DotProductExtExt calls: {}",
                pretty_integer(dot_product_ext_ext_calls)
            );
        }
        if dot_product_base_ext_calls > 0 {
            println!(
                "DotProductBaseExt calls: {}",
                pretty_integer(dot_product_base_ext_calls)
            );
        }
        let used_memory_cells = memory
            .0
            .iter()
            .skip(PUBLIC_INPUT_START + public_input.len())
            .filter(|&&x| x.is_some())
            .count();
        println!(
            "Memory usage: {:.1}%",
            used_memory_cells as f64 / runtime_memory_size as f64 * 100.0
        );
    }
    let no_vec_runtime_memory = ap - initial_ap;
    Ok(ExecutionResult {
        no_vec_runtime_memory,
        public_memory_size,
        memory,
        pcs,
        fps,
    })
}
