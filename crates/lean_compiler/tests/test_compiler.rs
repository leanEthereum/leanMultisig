use lean_compiler::*;
use lean_vm::*;
use multilinear_toolkit::prelude::BasedVectorSpace;
use rand::{Rng, SeedableRng, rngs::StdRng};
use utils::poseidon16_permute;

#[test]
#[should_panic]
fn test_duplicate_function_name() {
    let program = r#"
    fn a() -> 1 {
        return 0;
    }

    fn a() -> 1 {
        return 1;
    }

    fn main() {
        a();
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
#[should_panic]
fn test_duplicate_constant_name() {
    let program = r#"
    const A = 1;
    const A = 0;

    fn main() {
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
#[should_panic]
fn test_wrong_n_returned_vars_1() {
    let program = r#"
    fn main() {
        a, b = f();
        return;
    }

    fn f() -> 1 {
        return 0;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
#[should_panic]
fn test_wrong_n_returned_vars_2() {
    let program = r#"
    fn main() {
        a = f();
        return;
    }

    fn f() -> 1 {
        return 0, 1;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
#[should_panic]
fn test_no_return() {
    let program = r#"
    fn main() {
        a = f();
        return;
    }

    fn f() -> 1 {
    }

    fn g() -> 1 {
        return 0;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_assumed_return() {
    let program = r#"
    fn main() {
        a = f();
        return;
    }

    #![assume_always_returns]
    fn f() -> 1 {
        if 1 == 1 {
            return 0;
        } else {
            print(1);
        }
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_fibonacci_program() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        fibonacci(0, 1, 0, 30);
        return;
    }

    fn fibonacci(a, b, i, n) {
        if i == n {
            print(a);
            return;
        }
        fibonacci(b, a + b, i + 1, n);
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_edge_case_0() {
    let program = r#"
    fn main() {
        a = malloc(1);
        a[0] = 0;
        for i in 0..1 {
            x = 1 + a[i];
        }
        for i in 0..1 {
            y = 1 + a[i];
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_edge_case_1() {
    let program = r#"
    fn main() {
        a = malloc(1);
        a[0] = 0;
        assert a[8 - 8] == 0;
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_edge_case_2() {
    let program = r#"
    fn main() {
        for i in 0..5 unroll {
            x = i;
            print(x);
        }
        for i in 0..3 unroll {
            x = i;
            print(x);
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_decompose_bits() {
    let program = r#"
    fn main() {
        x = 2**20 - 1;
        a = malloc(31);
        print(a);
        hint_decompose_bits(x, a);
        for i in 0..20 {
            debug_assert a[i] == 1;
            assert a[i] == 1;
        }
        for i in 20..31 {
            assert a[i] == 0;
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_unroll() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        for i in 0..5 unroll {
            for j in i..2*i unroll {
                print(i, j);
            }
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_rev_unroll() {
    // a program to check the value of the 30th Fibonacci number (832040)
    let program = r#"
    fn main() {
        print(785 * 78 + 874 - 1);
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mini_program_0() {
    let program = r#"
    fn main() {
        for i in 0..5 {
            for j in i..2*i*(2+1) {
                print(i, j);
                if i == 4 {
                    if j == 7 {
                        break;
                    }
                }
            }
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mini_program_1() {
    let program = r#"
    const N = 10;

    fn main() {
        arr = malloc(N);
        fill_array(arr);
        print_array(arr);
        return;
    }

    fn fill_array(arr) {
        for i in 0..N {
            if i == 0 {
                arr[i] = 10;
            } else if i == 1 {
                arr[i] = 20;
            } else if i == 2 {
                arr[i] = 30;
            } else {
                i_plus_one = i + 1;
                arr[i] = i_plus_one;
            }
        }
        return;
    }

    fn print_array(arr) {
        for i in 0..N {
            arr_i = arr[i];
            print(arr_i);
        }
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mini_program_2() {
    let program = r#"
    fn main() {
        for i in 0..10 {
            for j in i..10 {
                for k in j..10 {
                    sum, prod = compute_sum_and_product(i, j, k);
                    if (sum == 10) {
                        print(i, j, k, prod);
                    }
                }
            }
        }
        return;
    }

    fn compute_sum_and_product(a, b, c) -> 2 {
        s1 = a + b;
        sum = s1 + c;
        p1 = a * b;
        product = p1 * c;
        return sum, product;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mini_program_3() {
    let program = r#"
    fn main() {
        a = public_input_start;
        b = a + 8;
        c = malloc(2*8);
        poseidon16(a, b, c, 0);

        for i in 0..8 {
            cc = c[i];
            print(cc);
        }
        for i in 0..8 {
            dd = c[i+8];
            print(dd);
        }
        return;
    }
   "#;
    let public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&public_input, &[]), false);

    let _ = dbg!(poseidon16_permute(public_input));
}

#[test]
fn test_inlined() {
    let program = r#"
    // Dot product precompile:
    const BE = 1; // base-extension
    const EE = 0; // extension-extension

    fn main() {
        x = 1;
        y = 2;
        i, j, k = func_1(x, y);
        assert i == 2;
        assert j == 3;
        assert k == 2130706432;

        g = malloc(8);
        h = malloc(8);
        for i in 0..8 {
            g[i] = i;
        }
        for i in 0..8 unroll {
            h[i] = i;
        }
        assert_eq_1(g, h);
        assert_eq_2(g, h);
        assert_eq_3(g, h);
        assert_eq_4(g, h);
        assert_eq_5(g, h);
        return;
    }

    fn func_1(a, b) inline -> 3 {
        x = a * b;
        y = a + b;
        return x, y, a - b;
    }

    fn assert_eq_1(x, y) {
        x_ptr = x;
        y_ptr = y;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }

    fn assert_eq_2(x, y) inline {
        x_ptr = x;
        y_ptr = y;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }
    fn assert_eq_3(x, y) inline {
        u = x + 7;
        assert_eq_1(u-7, y * 7 / 7);
        return;
    }
    fn assert_eq_4(x, y) {
        dot_product(x, pointer_to_one_vector, y, 1, EE);
        dot_product(x + 3, pointer_to_one_vector, y + 3, 1, EE);
        return;
    }
    fn assert_eq_5(x, y) inline {
        dot_product(x, pointer_to_one_vector, y, 1, EE);
        dot_product(x + 3, pointer_to_one_vector, y + 3, 1, EE);
        return;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_inlined_2() {
    let program = r#"
    fn main() {
        b = is_one();
        c = b;
        return;
    }

    fn is_one() inline -> 1 {
        if 1 {
            return 1;
        } else {
            return 0;
        }
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_match() {
    let program = r#"
    fn main() {
        for x in 0..3 unroll {
            func_match(x);
        }
        for x in 0..2 unroll {
            match x {
                0 => {
                    y = 10 * (x + 8);
                    z = 10 * y;
                    print(z);
                }
                1 => {
                    y = 10 * x;
                    z = func_2(y);
                    print(z);
                }
            }
        }
        return;
    }

    fn func_match(x) inline {
        match x {
            0 => {
                print(41);
            }
            1 => {
                y = func_1(x);
                print(y + 1);
            }
            2 => {
                y = 10 * x;
                print(y);
            }
        }
        return;
    }

    fn func_1(x) -> 1 {
        return x * x * x * x;
    }

    fn func_2(x) inline -> 1 {
        return x * x * x * x * x * x;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_match_shrink() {
    let program = r#"
    fn main() {
        match 1 {
            0 => {
                y = 90;
            }
            1 => {
                y = 10;
                z = func_2(y);
            }
        }
        return;
    }

    fn func_2(x) inline -> 1 {
        return x * x;
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

// #[test]
// fn inline_bug_mre() {
//     let program = r#"
//     fn main() {
//         boolean(0);
//         return;
//     }

//     fn boolean(a) inline -> 1 {
//         if a == 0 {
//             return 0;
//         }
//         return 1;
//     }
//    "#;
//     compile_and_run(program.to_string(), (&[], &[]));
// }

#[test]
fn test_const_functions_calling_const_functions() {
    // Test that const functions can call other const functions
    let program = r#"
    fn main() {
        y = compute_value(3);
        print(y);
        return;
    }

    fn compute_value(const n) -> 1 {
        result = complex_computation(n, 5);
        return result;
    }

    fn complex_computation(const a, const b) -> 1 {
        return a * a + b * b;
    }
    "#;

    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_inline_functions_calling_inline_functions() {
    let program = r#"
    fn main() {
        x = double(3);
        y = quad(x);
        print(y);
        return;
    }

    fn double(a) inline -> 1 {
        return a + a;
    }

    fn quad(b) inline -> 1 {
        result = double(b);
        return result + result;
    }
    "#;

    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_nested_inline_functions() {
    let program = r#"
    fn main() {
        result = level_one(3);
        print(result);
        return;
    }

    fn level_one(x) inline -> 1 {
        result = level_two(x);
        return result;
    }

    fn level_two(y) inline -> 1 {
        result = level_three(y);
        return result;
    }

    fn level_three(z) inline -> 1 {
        return z * z * z;
    }
    "#;

    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_const_and_nonconst_malloc_sharing_name() {
    let program = r#"
    fn main() {
        f(1);
        return;
    }

    fn f(n) {
        if 0 == 0 {
            res = malloc(2);
            res[1] = 0;
            return;
        } else {
            res = malloc(n * 1);
            return;
        }
    }
    "#;

    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_debug_assert_eq() {
    let program = r#"
    fn main() {
        a = 10;
        b = 20;
        debug_assert a * 2 == b;
        debug_assert a != b;
        debug_assert a < b;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[should_panic]
#[test]
fn test_debug_assert_eq_fail() {
    let program = r#"
    fn main() {
        a = 10;
        b = 25;
        debug_assert a * 2 == b;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[should_panic]
#[test]
fn test_debug_assert_not_eq_fail() {
    let program = r#"
    fn main() {
        a = 10;
        b = 10;
        debug_assert a != b;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[should_panic]
#[test]
fn test_debug_assert_lt_fail() {
    let program = r#"
    fn main() {
        a = 30;
        b = 20;
        debug_assert a < b;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_next_multiple_of() {
    let program = r#"
    fn main() {
        a = double(next_multiple_of(12, 8));
        assert a == 32;
        return;
    }

    fn double(const n) -> 1 {
        return next_multiple_of(n, n) * 2;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_const_array() {
    let program = r#"
    const FIVE = 5;
    const ARR = [4, FIVE, 4 + 2, 3 * 2 + 1];
    fn main() {
        for i in 1..len(ARR) unroll {
            x = i + 4;
            assert ARR[i] == x;
        }
        four = 4;
        assert len(ARR) == four;
        res = func(2);
        six = 6;
        assert res == six;
        nothing(ARR[0]);
        mem_arr = malloc(len(ARR));
        for i in 0..len(ARR) unroll {
            mem_arr[i] = ARR[i];
        }
        for i in 0..ARR[0] {
            print(2**ARR[0]);
        }
        print(2**ARR[1]);
        return;
    }

    fn func(const x) -> 1 {
        return ARR[x];
    }
    fn nothing(x) {
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_const_malloc_end_iterator_loop() {
    let program = r#"
    fn main() {
        x = malloc(2);
        x[0] = 3;
        x[1] = 5;
        for i in 0..2 unroll {
            for j in 0..x[i] {
                print(i, j);
            }
        }
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_array_return_targets() {
    let program = r#"
    fn main() {
        a = malloc(10);
        b = malloc(10);
        a[1], b[4] = get_two_values();
        assert a[1] == 42;
        assert b[4] == 99;
        
        i = 2;
        j = 3;
        a[i], b[j] = get_two_values();
        assert a[2] == 42;
        assert b[3] == 99;
        
        x, a[5] = get_two_values();
        assert x == 42;
        assert a[5] == 99;
        
        return;
    }

    fn get_two_values() -> 2 {
        return 42, 99;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_array_return_targets_with_expressions() {
    let program = r#"
    fn main() {
        arr = malloc(20);
        for i in 0..5 {
            arr[i * 2], arr[i * 2 + 1] = compute_pair(i);
        }
        assert arr[0] == 0;
        assert arr[1] == 0;
        assert arr[2] == 1;
        assert arr[3] == 2;
        assert arr[4] == 2;
        assert arr[5] == 4;
        return;
    }

    fn compute_pair(n) -> 2 {
        return n, n * 2;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn intertwined_unrolled_loops_and_const_function_arguments() {
    let program = r#"
        const ARR = [10, 100];
        fn main() {
            buff = malloc(3);
            buff[0] = 0;
            for i in 0..2 unroll {
                res = f1(ARR[i]);
                buff[i + 1] = res;
            }
            assert buff[2] == 1390320454;
            return;
        }

        fn f1(const x) -> 1 {
            buff = malloc(9);
            buff[0] = 1;
            for i in x..x+4 unroll {
                for j in i..i+2 unroll {
                    index = (i - x) * 2 + (j - i);
                    res = f2(i, j);
                    buff[index+1] = buff[index] * res;
                }
            }
            return buff[8];
        }

        fn f2(const x, const y) -> 1 {
            buff = malloc(7);
            buff[0] = 0;
            for i in x..x+2 unroll {
                for j in i..i+3 unroll {
                    index = (i - x) * 3 + (j - i);
                    buff[index+1] = buff[index] + i + j;
                }
            }
            return buff[4];
        }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_const_fibonacci() {
    let program = r#"
    fn main() {
        res = fib(8);
        assert res == 21;
        return;
    }
    fn fib(const n) -> 1 {
        if n == 0 {
            return 0;
        }
        if n == 1 {
            return 1;
        }
        a = fib(saturating_sub(n, 1));
        b = fib(saturating_sub(n, 2));
        return a + b;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_div_extension_field() {
    let program = r#"
        // Dot product precompile:
        const BE = 1; // base-extension
        const EE = 0; // extension-extension

        const DIM = 5;
        fn main() {
            n = public_input_start;
            d = public_input_start + DIM;
            q = public_input_start + 2 * DIM;
            computed_q_1 = div_ext_1(n, d);
            computed_q_2 = div_ext_2(n, d);
            assert_eq_ext(computed_q_2, q);
            assert_eq_ext(computed_q_1, q);
            return;
        }

        fn assert_eq_ext(x, y) {
            for i in 0..DIM unroll {
                assert x[i] == y[i];
            }
            return;
        }

        fn div_ext_1(n, d) -> 1 {
            quotient = malloc(DIM);
            dot_product(d, quotient, n, 1, EE);
            return quotient;
        }
        
        fn div_ext_2(n, d) -> 1 {
            quotient = malloc(DIM);
            dot_product(quotient, d, n, 1, EE);
            return quotient;
        }
    "#;

    let mut rng = StdRng::seed_from_u64(0);
    let n: EF = rng.random();
    let d: EF = rng.random();
    let q = n / d;
    let mut public_input = vec![];
    public_input.extend(n.as_basis_coefficients_slice());
    public_input.extend(d.as_basis_coefficients_slice());
    public_input.extend(q.as_basis_coefficients_slice());
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&public_input, &[]), false);
}

fn run_program_in_files(i: usize) {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let path = format!("{manifest_dir}/tests/program_{i}.snark");
    compile_and_run(&ProgramSource::Filepath(path), (&[], &[]), false);
}

#[test]
#[should_panic]
fn test_undefined_import() {
    run_program_in_files(0);
}

#[test]
#[should_panic]
fn test_imported_function_name_clash() {
    run_program_in_files(1);
}

#[test]
#[should_panic]
fn test_imported_constant_name_clash() {
    run_program_in_files(2);
}

#[test]
fn test_double_import_tolerance() {
    run_program_in_files(3);
}

#[test]
fn test_circular_import_tolerance() {
    run_program_in_files(4);
}

#[test]
#[should_panic]
fn test_no_main() {
    run_program_in_files(5);
}

#[test]
fn test_imports() {
    run_program_in_files(6);
}

#[test]
fn test_name_conflict() {
    let program = r#"
    fn main() {
        a = b();
        b = a();
        assert a + b == 30;
        return;
    }
    fn a() -> 1 {
        return 10;
    }
    fn b() -> 1 {
        return 20;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

// BUG here:

// #[test]
// fn test_num_files() {
//     let expected_num_files = 3; // program_6.snark imports foo.snark and bar.snark
//     let manifest_dir = env!("CARGO_MANIFEST_DIR");
//     let path = format!("{manifest_dir}/tests/program_6.snark");
//     let bytecode = compile_program(&ProgramSource::Filepath(path));
//     assert_eq!(bytecode.filepaths.len(), expected_num_files);
//     assert_eq!(bytecode.source_code.len(), expected_num_files);
// }

// TODO BUG

// #[test]
// fn bug() {
//     let program = r#"
//     fn main() {
//         x = func();
//         return;
//     }
//     fn func() -> 1 {
//         var a;
//         if 0 == 0 {
//             a = aux();
//         }
//         return a;
//     }

//     fn aux() inline -> 1 {
//         return 1;
//     }
//     "#;
//     compile_and_run(program.to_string(), (&[], &[]), false);
// }
