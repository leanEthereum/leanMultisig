use lean_compiler::SimpleLine;
use lean_compiler::{Expression, Line, SimpleExpr};
use lean_compiler::{
    compile_program, compile_to_intermediate_bytecode, compile_to_low_level_bytecode,
    parse_program, simplify_program,
};
use lean_vm::core::Label;
use lean_vm::execution::{execute_bytecode, execute_bytecode_helper};
use lean_vm::*;
use p3_field::PrimeCharacteristicRing;
use rand::Rng;
use rand_chacha::ChaCha20Rng;
use rand_chacha::rand_core::SeedableRng;
use rayon::iter::{IntoParallelRefIterator, ParallelIterator};
use std::collections::{BTreeMap, BTreeSet};
use utils::ToUsize;

fn critical_test_cases() -> BTreeSet<(usize, usize)> {
    let mut test_cases = BTreeSet::new();

    for t in 0..200 {
        for v in 0..t * 2 {
            test_cases.insert((v, t));
        }
        for v in 16777215..16777300 {
            test_cases.insert((v, t));
        }
    }

    test_cases
}

fn random_test_cases(num_test_cases: usize) -> BTreeSet<(usize, usize)> {
    let v_max = 16777215 * 2;
    let t_max = 65536;
    let mut rng = ChaCha20Rng::seed_from_u64(0);

    let mut test_cases = BTreeSet::new();

    for _ in 0..num_test_cases / 2 {
        let t = rng.random_range(0..t_max) as usize;
        let v = rng.random_range(0..v_max) as usize;
        test_cases.insert((v, t));
    }

    for _ in 0..num_test_cases / 2 {
        let t = rng.random_range(0..t_max) as usize;
        let v = rng.random_range(0..v_max) as usize;
        if v >= t {
            test_cases.insert((v, t));
        } else {
            test_cases.insert((t, v));
        }
    }

    test_cases
}

// TODO: create more test programs
fn range_check_program(value: usize, max: usize) -> String {
    let program = format!(
        r#"
    fn func(val) {{
        if 0 == 0 {{
            range_check(val, {max});
        }}
        abc = 0;
        range_check(abc, {max});
        return;
    }}

    fn main() {{
        val = {value};
        func(val);
        range_check(val, {max});
        range_check(val, {max});
        return;
    }}
    "#
    );
    program.to_string()
}

#[test]
fn test_compile_range_checks() {
    //// Run the tests serially for debugging
    //for (v, t) in range_check_test_cases() {
    //do_test_range_check(v, t, true);
    //}
    //println!("range_check_test_cases: {:?}", range_check_test_cases().len());

    // Run the tests in parallel
    let mut test_cases = critical_test_cases();
    test_cases.extend(random_test_cases(1000));
    println!("Running {} test cases", test_cases.len());
    test_cases.par_iter().for_each(|(v, t)| {
        do_test_range_check(*v, *t, false);
    });
}

fn do_test_range_check(v: usize, t: usize, verbose: bool) {
    let max_runner_memory_size: usize = 1 << 24;

    let public_input = &[];
    let private_input = &[];

    let program = range_check_program(v, t);
    let (bytecode, function_locations) = compile_program(&program, public_input, private_input);

    if verbose {
        println!("Range Check Test: v: {}, t: {} ==============", v, t);
        println!("Compiled bytecode: \n{}", bytecode);
        println!("ending_pc: {}", bytecode.ending_pc);
    }

    // Execute the bytecode with range checks already compiled
    let mut std_out = String::new();
    let mut instruction_history = ExecutionHistory::default();
    let result = execute_bytecode_helper(
        &bytecode,
        public_input,
        private_input,
        max_runner_memory_size / 2,
        &mut std_out,
        &mut instruction_history,
        false,
        &function_locations,
    );

    if v >= 16777216 || v >= t {
        if result.is_err() && verbose {
            println!("result: {}", result.as_ref().unwrap_err());
        }
        assert!(
            matches!(result, Err(RunnerError::OutOfMemory)),
            "range check failed to catch OOM"
        );
        if verbose {
            println!("Executed bytecode: OOM as expected");
        }
    } else {
        if result.is_err() && verbose {
            println!("result: {}", result.as_ref().unwrap_err());
        }
        assert!(result.is_ok());
        if verbose {
            println!("Executed bytecode: OK");
        }
    }
}

#[test]
fn test_range_check_execution() {
    do_test_range_check(0, 1, false);
}

/// Test that the range check keyword is parsed and compiled (steps a to c only).
#[test]
fn test_range_check_parsing_and_compilation() {
    let value_usize = 1;
    let max_usize = 2;
    let program = range_check_program(value_usize, max_usize);
    let (parsed_program, _function_locations) = parse_program(&program).unwrap();

    // Traverse through the parsed program and check that the range check is present
    let main_func = parsed_program.functions.get("main").unwrap();
    let mut found = false;
    for line in main_func.body.iter() {
        match line {
            Line::RangeCheck { value, max } => {
                match value {
                    Expression::Value(SimpleExpr::Var(v)) => {
                        assert_eq!(v, "val", "Range check value should be 'val'");
                        if let Some(max_val) = max.naive_eval() {
                            assert_eq!(
                                max_val.to_usize(),
                                max_usize,
                                "Range check max should be 2"
                            );
                        }
                    }
                    _ => assert!(
                        false,
                        "{}",
                        format!("Unexpected range check value type: {:?}", value)
                    ),
                }

                found = true;
            }
            _ => {}
        }
    }
    assert!(found, "Range check not found in the parsed program");

    found = false;
    let simple_program = simplify_program(parsed_program);
    let main_func = simple_program.functions.get("main").unwrap();

    // Traverse through the simplified program and check that the range check is present
    for line in main_func.instructions.iter() {
        match line {
            SimpleLine::RangeCheck { value, max } => {
                match value {
                    SimpleExpr::Var(v) => {
                        assert_eq!(v, "val", "Range check value should be 'val'");
                        if let Some(max_val) = max.naive_eval() {
                            assert_eq!(max_val.to_usize(), max_usize, "Range check max match");
                        }
                    }
                    _ => assert!(
                        false,
                        "{}",
                        format!("Unexpected range check value type: {:?}", value)
                    ),
                }
                found = true;
            }
            _ => {}
        }
    }
    assert!(found, "Range check not found in the simplified program");

    let intermediate_bytecode = compile_to_intermediate_bytecode(simple_program.clone()).unwrap();
    let compiled = compile_to_low_level_bytecode(intermediate_bytecode).unwrap();

    found = false;
    for (_pc, hints) in compiled.hints.iter() {
        for hint in hints {
            match hint {
                Hint::RangeCheck { value, max } => {
                    assert!(
                        matches!(value, MemOrFp::MemoryAfterFp { .. }),
                        "Range check value should be memory reference in low level bytecode"
                    );

                    match max {
                        MemOrConstant::MemoryAfterFp { .. } => {
                            assert!(
                                false,
                                "Range check max should be evaluable constant in low level bytecode"
                            );
                            unreachable!();
                        }
                        MemOrConstant::Constant(c) => {
                            assert_eq!(c.to_usize(), max_usize, "Range check max mismatch");
                        }
                    }
                    found = true;
                }
                _ => {}
            }
        }
    }

    assert!(found, "Range check not found in the intermediate bytecode");
}

// The following tests are on manually written bytecode that implement the range-check technique.
// In practice, the compiler compiles the range_check keyword via compile_range_checks() in
// crates/lean_compiler/src/d_compile_range_checks.rs.

// Passes if the range check works when v < t
fn do_test_valid_range_check(v: usize, t: usize) {
    let result = range_check(v, t);
    if result.is_err() {
        println!("Error: {}", result.unwrap_err());
        assert!(false, "Range check failed");
    } else {
        assert!(result.is_ok());
    }
}

// Passes if the range check fails with OOM when v >= t
fn do_test_invalid_range_check(v: usize, t: usize) {
    let result = range_check(v, t); // should OOM
    if result.is_ok() {
        println!("Execution complete but the range check failed to OOM");
        assert!(false, "range check failed to catch OOM");
    }
    assert!(matches!(&result, Err(RunnerError::OutOfMemory)));
}

#[test]
fn test_valid_range_check() {
    // Check t = 70, v = 0..70
    let t = 70;
    for v in 0..t {
        do_test_valid_range_check(v, t);
    }

    // Check 0..[63, 64, 65]
    for t in vec![63, 64, 65] {
        for v in 0..t {
            do_test_valid_range_check(v, t);
        }
    }

    do_test_valid_range_check(64, 65);

    do_test_valid_range_check(0, 16777216);
    do_test_valid_range_check(64, 16777216);
    do_test_valid_range_check(16777215, 16777216);
}

// Should OOM since v >= M
#[test]
fn test_invalid_range_check_1() {
    let v = 16777216;
    for t in 0..70 {
        do_test_invalid_range_check(v, t);
    }
}

// Should OOM since t - 1 - v >= M
#[test]
fn test_invalid_range_check_2() {
    let v = 100;
    let t = 16777216 + 1 + v;
    do_test_invalid_range_check(v, t);
}

// Should OOM since v >= t
#[test]
fn test_invalid_range_check_3() {
    let t = 200;
    for v in 200..300 {
        do_test_invalid_range_check(v, t);
    }
}

// Should OOM since v == t
#[test]
fn test_invalid_range_check_4() {
    for i in 1..100 {
        do_test_invalid_range_check(i, i);
    }
}

// Should OOM since v > 0
#[test]
fn test_invalid_range_check_5() {
    for v in 1..100 {
        do_test_invalid_range_check(v, 0);
    }
}

#[test]
fn test_invalid_range_check_6() {
    let t = 0;
    for v in 0..70 {
        do_test_invalid_range_check(v, t);
    }
    do_test_invalid_range_check(16777215, t);
}

#[test]
fn test_invalid_range_check_7() {
    for v in 0..10 {
        do_test_invalid_range_check(16777216 + v, 16777216);
    }
}

#[test]
fn test_deref() {
    let x = 1000;
    let y = 1001;
    let v_p = 1006;
    let v_q = 1007;
    let val = F::from_usize(123);
    let starting_frame_memory = 5;
    let mut instructions = vec![];
    let mut hints = BTreeMap::new();

    // Store v in m[fp + x] by setting a pointer m[fp + vp] = fp + x and using deref to store
    // v in m[m[fp + v_p] + 0]
    instructions.push(
        // computation: m[fp + v_p] = fp + x
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(x)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: v_p },
        },
    );

    instructions.push(
        // deref: val = m[m[fp + v_p] + 0] = m[fp + x]
        Instruction::Deref {
            shift_0: v_p,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(val),
        },
    );

    instructions.push(
        // computation: m[fp + v_q] = fp + y
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(y)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: v_q },
        },
    );

    instructions.push(
        // deref: val = m[m[fp + v_q] + 0] = m[fp + y]
        Instruction::Deref {
            shift_0: v_q,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(val),
        },
    );

    hints.insert(
        instructions.len(),
        vec![
            Hint::Print {
                line_info: "m[fp + 1000]".to_string(),
                content: vec![MemOrConstant::MemoryAfterFp { offset: 1000 }],
            },
            Hint::Print {
                line_info: "m[fp + 1001]".to_string(),
                content: vec![MemOrConstant::MemoryAfterFp { offset: 1001 }],
            },
        ],
    );

    instructions.push(Instruction::Deref {
        shift_0: v_q,
        shift_1: 0,
        res: MemOrFpOrConstant::MemoryAfterFp { offset: 1000 },
    });

    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        label: Label::custom("test_jump_1"),
        dest: MemOrConstant::Constant(F::from_usize(instructions.len() + 1)),
        updated_fp: MemOrFp::Fp,
    });
    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        label: Label::custom("test_jump_2"),
        dest: MemOrConstant::Constant(F::from_usize(0)),
        updated_fp: MemOrFp::Fp,
    });

    let ending_pc = instructions.len() - 1;
    let bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory,
        ending_pc,
    };
    let execution_result = execute_bytecode(
        &bytecode,
        &[],                                // public input
        &[],                                // private input
        "",                                 // no source code for debug
        &std::collections::BTreeMap::new(), // no function locations
        1 << 23,                            // no_vec_runtime_memory
        false,                              // no profiler
    );

    // execution_result is now ExecutionResult struct, not a Result
    assert!(execution_result.pcs.len() > 0); // Basic check that execution completed
}

fn range_check(v: usize, t: usize) -> Result<ExecutionResult, RunnerError> {
    let starting_frame_memory = 5;
    let val = F::from_usize(v);

    // In the final version, these values will have to be set after a first execution pass
    let x = 1000;
    let i = 1003;
    let j = 1004;
    let k = 1005;
    let v_p = 1006;
    let t_p = 1007;

    let mut instructions = vec![];
    let hints = BTreeMap::new();

    // Store v in m[fp + x] by setting a pointer m[fp + vp] = fp + x and using deref to store
    // v in m[m[fp + v_p] + 0]
    instructions.push(
        // computation: m[fp + v_p] = fp + x
        Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::Constant(F::from_usize(x)),
            arg_c: MemOrFp::Fp,
            res: MemOrConstant::MemoryAfterFp { offset: v_p },
        },
    );

    instructions.push(
        // deref: val = m[m[fp + v_p] + 0] = m[fp + x]
        Instruction::Deref {
            shift_0: v_p,
            shift_1: 0,
            res: MemOrFpOrConstant::Constant(val),
        },
    );

    // Store t - 1 in m[fp + t_p] using constraint solving
    instructions.push(Instruction::Computation {
        operation: Operation::Add,
        arg_a: MemOrConstant::Constant(F::ONE),        // 1
        arg_c: MemOrFp::MemoryAfterFp { offset: t_p }, // m[fp + t_p] is unknown, so it will solve
        // to t - 1
        res: MemOrConstant::Constant(F::from_usize(t)),
    });

    // Range check step 1:
    // Ensure that m[fp + i] == m[m[fp + x] + 0] aka m[val]
    // Fails if val >= M because of OOM
    let step_1_res = if v == 64 || v == 65 {
        MemOrFpOrConstant::Constant(F::ZERO)
    } else if v < 64 {
        MemOrFpOrConstant::MemoryAfterFp { offset: i }
    } else if v >= 16777216 {
        MemOrFpOrConstant::MemoryAfterFp { offset: v_p }
    } else {
        MemOrFpOrConstant::MemoryAfterFp { offset: v_p }
    };

    instructions.push(Instruction::Deref {
        shift_0: x,
        shift_1: 0,
        res: step_1_res,
    });

    // Range check step 2: Using ADD, ensure (via constraint-solving):
    // m[fp + j] + m[m[fp + x]] = (t - 1)
    // m[fp + j] = (t - 1) - m[m[fp + x]]
    instructions.push(Instruction::Computation {
        operation: Operation::Add,
        arg_a: MemOrConstant::MemoryAfterFp { offset: j }, // Unknown: m[fp + j] will be solved to
        // (t-1) - m[val]
        arg_c: MemOrFp::MemoryAfterFp { offset: x }, // Known:   m[fp + x] = m[val]
        res: MemOrConstant::MemoryAfterFp { offset: t_p }, // Known:   t - 1
    });

    // If m[m[fp + j]] = m[t - 1 - v] is already initialised, set m[fp + k] = m[fp + j]
    if (t > v && t - 1 - v >= 64) || (t <= v) {
        instructions.push(Instruction::Computation {
            operation: Operation::Add,
            arg_a: MemOrConstant::MemoryAfterFp { offset: k }, // Unknown: m[fp + k]
            arg_c: MemOrFp::MemoryAfterFp { offset: j },       // Known:   m[fp + j]
            res: MemOrConstant::Constant(F::from_usize(0)),    // Known:   0
        });
    }

    // Range check step 3: ensure `m[m[fp + j]] = m[fp + k]`
    instructions.push(Instruction::Deref {
        shift_0: j,
        shift_1: 0,
        res: MemOrFpOrConstant::MemoryAfterFp { offset: k },
    });

    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        label: Label::custom("test_jump_3"),
        dest: MemOrConstant::Constant(F::from_usize(instructions.len() + 1)),
        updated_fp: MemOrFp::Fp,
    });
    instructions.push(Instruction::Jump {
        condition: MemOrConstant::Constant(F::ONE),
        label: Label::custom("test_jump_4"),
        dest: MemOrConstant::Constant(F::from_usize(0)),
        updated_fp: MemOrFp::MemoryAfterFp { offset: 0 },
    });

    let ending_pc = instructions.len() - 1;
    let bytecode = Bytecode {
        instructions,
        hints,
        starting_frame_memory,
        ending_pc,
    };

    // Execute the bytecode
    let execution_result = execute_bytecode_helper(
        &bytecode,
        &[],
        &[],
        1 << 23,
        &mut String::new(),
        &mut ExecutionHistory::new(),
        false,
        &BTreeMap::new(),
    )?;

    Ok(execution_result)
}
