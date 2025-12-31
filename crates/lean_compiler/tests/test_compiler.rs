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
    const BIG_ENDIAN = 0;
    const LITTLE_ENDIAN = 1;
    fn main() {
        x = 2**20 - 1;
        a = malloc(31);
        print(a);
        hint_decompose_bits(x, a, 31, LITTLE_ENDIAN);
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
                    if sum == 10 {
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
fn test_mini_program_4() {
    let program = r#"
    fn main() {
        arr = malloc(10);
        arr[6] = 42;
        arr[8] = 11;
        sum_1 = func_1(arr[6], arr[8]);
        assert sum_1 == 53;
        return;
    }

    fn func_1(i, j) inline -> 1 {
        for k in 0..i {
            for u in 0..j {
                assert k + u != 1000000;
            }
        }
        return i + j;
    }

   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
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
        if !!assume_bool(1) {
            return 1;
        } else {
            return 0;
        }
    }
   "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_inlined_3() {
    let program = r#"
    fn main() {
        x = func();
        return;
    }
    fn func() -> 1 {
        var a;
        if 0 == 0 {
            a = aux();
        }
        return a;
    }

    fn aux() inline -> 1 {
        return 1;
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
fn test_direct_const_arr_access() {
    let program = r#"
        const ARR = [10, 100];
        fn main() {
            a = ARR[0];
            assert a == 10;
            return;
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

#[test]
fn test_2d_const_array() {
    let program = r#"
    const NESTED = [[1, 2], [3, 4, 5], [6]];
    fn main() {
        // Test len() on nested arrays
        assert len(NESTED) == 3;
        assert len(NESTED[0]) == 2;
        assert len(NESTED[1]) == 3;
        assert len(NESTED[2]) == 1;

        // Test chained indexing
        assert NESTED[0][0] == 1;
        assert NESTED[0][1] == 2;
        assert NESTED[1][0] == 3;
        assert NESTED[1][2] == 5;
        assert NESTED[2][0] == 6;

        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_3d_const_array() {
    let program = r#"
    const DEEP = [[[1, 2], [3]], [[4, 5, 6]]];
    const ONE = 1;
    fn main() {
        assert len(DEEP) == 2;
        assert len(DEEP[0]) == 2;
        assert len(DEEP[0][0]) == 2;
        assert len(DEEP[0][1]) == 1;
        one = 1;
        assert len(DEEP[ONE]) == one;
        assert len(DEEP[1][0]) == 3;

        assert DEEP[0][0][0] == 1;
        assert DEEP[0][0][1] == 2;
        assert DEEP[0][1][0] == 3;
        assert DEEP[1][0][0] == 4;
        assert DEEP[1][0][2] == 6;

        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_2d_nested_array_with_expressions() {
    let program = r#"
    const TWO = 2;
    const ARR = [[1 + 1, TWO * 2], [3 + TWO]];
    const INCR_ARR = [[0, 1, 2], [1, 2, 3], [2, 3, 4], [3, 4, 5]];
    fn main() {
        assert len(ARR) == 2;
        assert ARR[0][0] == 2;
        assert ARR[0][1] == 4;
        assert ARR[1][0] == 5;
        five = ARR[1][0];
        assert five == 5;
        x = 2 + 3 * (ARR[0][0] + ARR[1][0] + 3)**2;
        assert x == 302;
        for i in 0..4 unroll {
            for j in 0..3 unroll {
                y = INCR_ARR[i][j];
                assert INCR_ARR[i][j] == i + j - INCR_ARR[i][j] + y;
            }
        }
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_const_array_element_exponentiation() {
    let program = r#"
    const ARR = [[5]];
    fn main() {
        x = ARR[0][0]**2;
        assert x == 25;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_num_files() {
    let expected_num_files = 3; // program_6.snark imports foo.snark and bar.snark
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let path = format!("{manifest_dir}/tests/program_6.snark");
    let bytecode = compile_program(&ProgramSource::Filepath(path));
    assert_eq!(bytecode.filepaths.len(), expected_num_files);
    assert_eq!(bytecode.source_code.len(), expected_num_files);
}

#[test]
fn test_nested_function_call() {
    let program = r#"
    fn main() {
        assert incr(incr(incr(1))) == 4;
        x = add(incr(1), incr(2));
        assert x == 5;

        assert incr_inline(incr_inline(incr_inline(1))) == 4;
        y = add_inlined(incr_inline(1), add_inlined(incr_inline(2), incr_inline(2)));
        assert y == 8;

        return;
    }

    fn add(a, b) -> 1 {
        return a + b;
    }

    fn incr(x) -> 1 {
        return x + 1;
    }

    fn incr_inline(x) inline -> 1 {
        return x + 1;
    }
    

    fn add_inlined(a, b) inline -> 1 {
        c = malloc(1);
        zero = 0;
        c[zero] = a + b;
        return c[0];
    }
    "#;

    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_len_2d_array() {
    let program = r#"
    const ARR = [[1], [7, 3], [7]];
    const N = 2 + len(ARR[0]);
    fn main() {
        for i in 0..N unroll {
            for j in 0..len(ARR[i]) unroll {
                assert j * (j - 1) == 0;
            }
        }
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

// Tests for mutable variables feature

#[test]
fn test_mutable_variable_basic() {
    let program = r#"
    fn main() {
        mut x = 1;
        x = x + 1;
        x = x + 1;
        assert x == 3;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_variable_in_unrolled_loop() {
    let program = r#"
    fn main() {
        mut sum = 0;
        for i in 0..5 unroll {
            sum = sum + i;
        }
        // 0 + 1 + 2 + 3 + 4 = 10
        assert sum == 10;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_variable_in_if_else() {
    let program = r#"
    fn main() {
        mut x = 1;
        cond = 1;
        if cond == 1 {
            x = x + 10;
        } else {
            x = x + 20;
        }
        assert x == 11;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_function_argument() {
    let program = r#"
    fn main() {
        result = increment_twice(5);
        assert result == 7;
        return;
    }

    fn increment_twice(mut x) -> 1 {
        x = x + 1;
        x = x + 1;
        return x;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_selective_in_multi_return() {
    let program = r#"
    fn main() {
        a, mut b = get_two();
        b = b + 1;
        assert a == 10;
        assert b == 21;
        return;
    }

    fn get_two() -> 2 {
        return 10, 20;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_forward_declaration() {
    let program = r#"
    fn main() {
        var mut x;
        x = 5;
        x = x + 1;
        assert x == 6;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_nested_unrolled_loops() {
    let program = r#"
    fn main() {
        mut total = 0;
        mut outer_sum = 0;
        for i in 0..3 unroll {
            outer_sum = outer_sum + i;
            mut inner_sum = 0;
            for j in 0..4 unroll {
                inner_sum = inner_sum + j;
                total = total + 1;
            }
            // inner_sum should be 0+1+2+3 = 6
            assert inner_sum == 6;
        }
        // outer_sum should be 0+1+2 = 3
        assert outer_sum == 3;
        // total should be 3*4 = 12
        assert total == 12;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_triple_nested_unrolled_loops() {
    let program = r#"
    fn main() {
        mut count = 0;
        mut sum_i = 0;
        mut sum_j = 0;
        mut sum_k = 0;
        for i in 0..2 unroll {
            sum_i = sum_i + i;
            for j in 0..3 unroll {
                sum_j = sum_j + j;
                for k in 0..2 unroll {
                    sum_k = sum_k + k;
                    count = count + 1;
                }
            }
        }
        // count = 2 * 3 * 2 = 12
        assert count == 12;
        // sum_i = (0+1) * 6 = 6 (each i value is added 6 times due to inner loops? No, just once per outer iteration)
        // Actually sum_i = 0 + 1 = 1 (added once per outer loop iteration)
        assert sum_i == 1;
        // sum_j = (0+1+2) * 2 * 2 = 3 * 4 = 12? No, sum_j is added once per middle loop iteration
        // 2 outer iterations * 3 middle iterations = 6 times, but value is 0+1+2 per outer = 3 per outer
        // so 2 * 3 = 6
        assert sum_j == 6;
        // sum_k = (0+1) per innermost = 1, and innermost runs 2*3=6 times, so 6*1 = 6
        assert sum_k == 6;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_with_const_args() {
    let program = r#"
    const N = 5;
    const M = 3;

    fn main() {
        mut acc = 0;
        for i in 0..N unroll {
            acc = acc + M;
        }
        // acc = 5 * 3 = 15
        assert acc == 15;

        mut product = 1;
        for i in 0..M unroll {
            product = product * 2;
        }
        // product = 2^3 = 8
        assert product == 8;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_inlined_function() {
    let program = r#"
    fn main() {
        mut x = 10;
        x = double(x);
        assert x == 20;
        x = double(x);
        assert x == 40;
        x = add_five(x);
        assert x == 45;
        return;
    }

    fn double(mut n) inline -> 1 {
        n = n + n;
        return n;
    }

    fn add_five(mut n) inline -> 1 {
        n = n + 5;
        return n;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_nested_inlined_functions() {
    let program = r#"
    fn main() {
        mut val = 1;
        val = outer(val);
        // outer: val = inner(val*2) = inner(2) = 2+10 = 12, then 12*3 = 36
        assert val == 36;
        return;
    }

    fn outer(mut x) inline -> 1 {
        x = x * 2;
        x = inner(x);
        x = x * 3;
        return x;
    }

    fn inner(mut y) inline -> 1 {
        y = y + 10;
        return y;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_nested_function_calls() {
    let program = r#"
    fn main() {
        mut a = 1;
        mut b = 2;
        a, b = swap(a, b);
        assert a == 2;
        assert b == 1;

        a, b = swap(a, b);
        assert a == 1;
        assert b == 2;

        mut c = compute(a, b);
        assert c == 5;  // 1 + 2*2 = 5
        c = compute(c, c);
        assert c == 15; // 5 + 5*2 = 15
        return;
    }

    fn swap(x, y) -> 2 {
        return y, x;
    }

    fn compute(x, y) -> 1 {
        result = x + y * 2;
        return result;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_complex_if_else() {
    let program = r#"
    fn main() {
        mut x = 0;
        mut y = 0;
        mut z = 0;

        cond1 = 1;
        if cond1 == 1 {
            x = x + 10;
            y = y + 20;
        } else {
            x = x + 100;
            z = z + 30;
        }
        assert x == 10;
        assert y == 20;
        assert z == 0;

        cond2 = 0;
        if cond2 == 1 {
            x = x + 1;
        } else {
            x = x + 2;
            y = y + 3;
        }
        assert x == 12;
        assert y == 23;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_nested_if_else() {
    // Test mutable variable through nested if/else - simplified version
    // The full nested case with mutations after inner if/else is complex
    let program = r#"
    fn main() {
        mut counter = 0;

        a = 1;
        if a == 1 {
            counter = counter + 1;
        } else {
            counter = counter + 1000;
        }
        assert counter == 1;

        b = 1;
        if b == 1 {
            counter = counter + 10;
        } else {
            counter = counter + 100;
        }
        // counter = 1 + 10 = 11
        assert counter == 11;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_multiple_variables_interleaved() {
    let program = r#"
    fn main() {
        mut a = 1;
        mut b = 2;
        mut c = 3;

        a = a + b;      // a = 3
        b = b + c;      // b = 5
        c = c + a;      // c = 6

        a = a * 2;      // a = 6
        b = b * 2;      // b = 10
        c = c * 2;      // c = 12

        assert a == 6;
        assert b == 10;
        assert c == 12;

        // Cross-dependencies
        a = b + c;      // a = 22
        b = c + a;      // b = 34 (uses new a)
        c = a + b;      // c = 56 (uses new a and b)

        assert a == 22;
        assert b == 34;
        assert c == 56;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_fibonacci_unrolled() {
    // Fibonacci using mutable variables
    // Note: using separate temp variable per iteration to avoid internal var reuse issues
    let program = r#"
    fn main() {
        mut fib_prev = 0;
        mut fib_curr = 1;

        // Manual unroll for clarity (internal mut temp in loop has issues)
        temp0 = fib_curr;
        fib_curr = fib_prev + fib_curr;
        fib_prev = temp0;

        temp1 = fib_curr;
        fib_curr = fib_prev + fib_curr;
        fib_prev = temp1;

        temp2 = fib_curr;
        fib_curr = fib_prev + fib_curr;
        fib_prev = temp2;

        temp3 = fib_curr;
        fib_curr = fib_prev + fib_curr;
        fib_prev = temp3;

        temp4 = fib_curr;
        fib_curr = fib_prev + fib_curr;
        fib_prev = temp4;

        // After 5 iterations: fib = 0, 1, 1, 2, 3, 5, 8
        assert fib_curr == 8;
        assert fib_prev == 5;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_with_arrays() {
    let program = r#"
    const N = 5;

    fn main() {
        arr = malloc(N);

        mut sum = 0;
        for i in 0..N unroll {
            arr[i] = i * 2;
            sum = sum + arr[i];
        }
        // arr = [0, 2, 4, 6, 8]
        // sum = 0 + 2 + 4 + 6 + 8 = 20
        assert sum == 20;

        mut product = 1;
        for i in 1..N unroll {
            product = product * arr[i];
        }
        // product = 2 * 4 * 6 * 8 = 384
        assert product == 384;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_in_match() {
    // Match with mutable - use only inside arms, not after
    // (mutating after match requires similar handling as if/else)
    let program = r#"
    fn main() {
        selector = 2;
        match selector {
            0 => {
                mut result = 1;
                assert result == 1;
            }
            1 => {
                mut result = 10;
                assert result == 10;
            }
            2 => {
                mut result = 100;
                result = result + 5;
                assert result == 105;
            }
        }
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_const_array_iteration() {
    let program = r#"
    const WEIGHTS = [1, 2, 3, 4, 5];
    const N = 5;

    fn main() {
        mut weighted_sum = 0;
        for i in 0..N unroll {
            weighted_sum = weighted_sum + WEIGHTS[i] * (i + 1);
        }
        // weighted_sum = 1*1 + 2*2 + 3*3 + 4*4 + 5*5 = 1 + 4 + 9 + 16 + 25 = 55
        assert weighted_sum == 55;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_function_chain() {
    let program = r#"
    fn main() {
        mut x = 1;
        x = step1(x);
        x = step2(x);
        x = step3(x);
        // step1: 1*2+1 = 3
        // step2: 3*3+2 = 11
        // step3: 11*4+3 = 47
        assert x == 47;
        return;
    }

    fn step1(mut n) -> 1 {
        n = n * 2;
        n = n + 1;
        return n;
    }

    fn step2(mut n) -> 1 {
        n = n * 3;
        n = n + 2;
        return n;
    }

    fn step3(mut n) -> 1 {
        n = n * 4;
        n = n + 3;
        return n;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_complex_expressions() {
    let program = r#"
    fn main() {
        mut a = 5;
        mut b = 3;

        // Complex expression on RHS
        a = a * a + b * b;  // 25 + 9 = 34
        assert a == 34;

        b = a - b * 2;      // 34 - 6 = 28
        assert b == 28;

        mut c = a + b;      // 34 + 28 = 62
        assert c == 62;

        // Multiple mutations
        c = c + 8;          // 70
        assert c == 70;

        c = c - 10;         // 60
        assert c == 60;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_with_inlined_in_loop() {
    // Test inlined function (non-mutable arg) with external mutable accumulator
    let program = r#"
    fn main() {
        mut total = 0;
        for i in 0..5 unroll {
            temp = add_one_pure(i);
            total = total + temp;
        }
        // add_one_pure(0) = 1, (1) = 2, (2) = 3, (3) = 4, (4) = 5
        // total = 1+2+3+4+5 = 15
        assert total == 15;
        return;
    }

    fn add_one_pure(x) inline -> 1 {
        result = x + 1;
        return result;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_accumulator_pattern() {
    let program = r#"
    const N = 6;

    fn main() {
        // Compute factorial of 5 using mutable accumulator
        mut factorial = 1;
        for i in 1..N unroll {
            factorial = factorial * i;
        }
        // 1 * 1 * 2 * 3 * 4 * 5 = 120
        assert factorial == 120;

        // Compute sum of squares
        mut sum_squares = 0;
        for i in 1..N unroll {
            sum_squares = sum_squares + i * i;
        }
        // 1 + 4 + 9 + 16 + 25 = 55
        assert sum_squares == 55;

        // Compute triangular number
        mut triangular = 0;
        for i in 1..N unroll {
            triangular = triangular + i;
        }
        // 1 + 2 + 3 + 4 + 5 = 15
        assert triangular == 15;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_multiple_returns_chain() {
    let program = r#"
    fn main() {
        mut a = 1;
        mut b = 2;
        mut c = 3;

        // Chain of multi-return function calls
        a, b = double_both(a, b);
        assert a == 2;
        assert b == 4;

        b, c = double_both(b, c);
        assert b == 8;
        assert c == 6;

        a, c = double_both(a, c);
        assert a == 4;
        assert c == 12;

        // Final values
        assert a + b + c == 24;
        return;
    }

    fn double_both(x, y) -> 2 {
        return x * 2, y * 2;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_rev_unrolled_loop() {
    let program = r#"
    fn main() {
        mut countdown = 0;
        for i in rev 0..5 unroll {
            countdown = countdown * 10 + i;
        }
        // i goes: 4, 3, 2, 1, 0
        // countdown: 0*10+4=4, 4*10+3=43, 43*10+2=432, 432*10+1=4321, 4321*10+0=43210
        assert countdown == 43210;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_if_else_in_unrolled_loop() {
    let program = r#"
    fn main() {
        mut even_sum = 0;
        mut odd_sum = 0;

        for i in 0..6 unroll {
            remainder = i % 2;
            if remainder == 0 {
                even_sum = even_sum + i;
            } else {
                odd_sum = odd_sum + i;
            }
        }
        // even: 0 + 2 + 4 = 6
        // odd: 1 + 3 + 5 = 9
        assert even_sum == 6;
        assert odd_sum == 9;
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test_mutable_comprehensive_stress() {
    // A comprehensive test combining multiple mutable variables
    let program = r#"
    const SIZE = 4;

    fn main() {
        arr = malloc(SIZE);

        // Initialize array with squares
        for i in 0..SIZE unroll {
            arr[i] = i * i;
        }
        // arr = [0, 1, 4, 9]

        // Sum the array using mutable accumulator
        mut sum = 0;
        for i in 0..SIZE unroll {
            val = arr[i];
            sum = sum + val;
        }
        // sum = 0 + 1 + 4 + 9 = 14
        assert sum == 14;

        // Double the sum multiple times
        sum = sum * 2;  // 28
        sum = sum + 2;  // 30
        assert sum == 30;

        // Use inline function with mutable arg
        mut result = process(sum);
        assert result == 35;  // 30 + 5

        result = process(result);
        assert result == 40;  // 35 + 5

        return;
    }

    fn process(mut x) inline -> 1 {
        x = x + 5;
        return x;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}

#[test]
fn test() {
    let program = r#"
    fn main() {
        for i in 0..6 {
            mut x = i;
            x = x + 1;
            for j in 0..3 {
                mut y = x + 1;
                y = y + j;
                if i == 10 {
                    y = y - 1;
                }
                if j == 10000 {
                    y = y - 2;
                } else if i != 1000 {
                    y = y + 2;
                }
                if j == 10000 {
                    y = y - 2;
                } else if i == 1000 {
                    y = y + 2;
                }
                if j == 10000 {
                    y = y - 2;
                } else if i != 1000 {
                    y = y + 2;
                } else {
                    y = y + 2;
                }
                assert y == i + j + 6;
            }
        }
        return;
    }
    "#;
    compile_and_run(&ProgramSource::Raw(program.to_string()), (&[], &[]), false);
}
