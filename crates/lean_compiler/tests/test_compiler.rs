use lean_compiler::*;
use lean_vm::*;
use utils::{poseidon16_permute, poseidon24_permute};

const DEFAULT_NO_VEC_RUNTIME_MEMORY: usize = 1 << 15;

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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}

#[test]
fn test_mini_program_3() {
    let program = r#"
    fn main() {
        a = public_input_start / 8;
        b = a + 1;
        c = malloc_vec(2);
        poseidon16(a, b, c, 0);

        c_shifted = c * 8;
        d_shifted = (c + 1) * 8;

        for i in 0..8 {
            cc = c_shifted[i];
            print(cc);
        }
        for i in 0..8 {
            dd = d_shifted[i];
            print(dd);
        }
        return;
    }
   "#;
    let public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&public_input, &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );

    let _ = dbg!(poseidon16_permute(public_input));
}

#[test]
fn test_mini_program_4() {
    let program = r#"
    fn main() {
        a = public_input_start / 8;
        c = a + 2;
        f = malloc_vec(1);
        poseidon24(a, c, f);

        f_shifted = f * 8;
        for j in 0..8 {
            print(f_shifted[j]);
        }
        return;
    }
   "#;
    let public_input: [F; 24] = (0..24).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&public_input, &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );

    dbg!(&poseidon24_permute(public_input)[16..]);
}

#[test]
fn test_mini_program_5() {
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}

#[test]
fn test_inlined() {
    let program = r#"
    fn main() {
        x = 1;
        y = 2;
        i, j, k = func_1(x, y);
        assert i == 2;
        assert j == 3;
        assert k == 2130706432;

        g = malloc_vec(1);
        h = malloc_vec(1);
        g_ptr = g * 8;
        h_ptr = h * 8;
        for i in 0..8 {
            g_ptr[i] = i;
        }
        for i in 0..8 unroll {
            h_ptr[i] = i;
        }
        assert_vectorized_eq_1(g, h);
        assert_vectorized_eq_2(g, h);
        assert_vectorized_eq_3(g, h);
        assert_vectorized_eq_4(g, h);
        assert_vectorized_eq_5(g, h);
        return;
    }

    fn func_1(a, b) inline -> 3 {
        x = a * b;
        y = a + b;
        return x, y, a - b;
    }

    fn assert_vectorized_eq_1(x, y) {
        x_ptr = x * 8;
        y_ptr = y * 8;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }

    fn assert_vectorized_eq_2(x, y) inline {
        x_ptr = x * 8;
        y_ptr = y * 8;
        for i in 0..4 unroll {
            assert x_ptr[i] == y_ptr[i];
        }
        for i in 4..8 {
            assert x_ptr[i] == y_ptr[i];
        }
        return;
    }
    fn assert_vectorized_eq_3(x, y) inline {
        u = x + 7;
        assert_vectorized_eq_1(u-7, y * 7 / 7);
        return;
    }
    fn assert_vectorized_eq_4(x, y) {
        dot_product_ee(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product_ee(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
    fn assert_vectorized_eq_5(x, y) inline {
        dot_product_ee(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product_ee(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
   "#;
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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

    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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

    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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

    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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

    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}

fn run_program_in_files(i: usize) {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let path = format!("{manifest_dir}/tests/program_{i}.snark");
    compile_and_run(
        &ProgramSource::Filepath(path),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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

    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
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
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}

#[test]
fn test_nested_matches() {
    let program = r#"
    fn main() {
        assert test_func(0, 0) == 6;
        assert test_func(1, 0) == 3;
        return;
    }

    fn test_func(a, b) -> 1 {
        x = 1;
    
        var mut_x_2;
        match a {
            0 => {            
                var mut_x_1;
                mut_x_1 = x + 2;
                match b {
                    0 => {                    
                        mut_x_2 = mut_x_1 + 3;
                    }
                }
            }
            1 => {
                mut_x_2 = x + 2;
            }
        }

        return mut_x_2;
    }
    "#;
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}

#[test]
fn test_deeply_nested_match() {
    // Test with 3 levels of nesting, multiple arms, and variables at each level
    let program = r#"
    fn main() {
        // Test each combination with expected values
        // (0,0,0): base=1000, local_a=5, local_b=8, inner_val=1008
        assert compute(0, 0, 0) == 1008;
        // (0,0,1): base=1000, local_a=5, local_b=8, inner_val=1009
        assert compute(0, 0, 1) == 1009;
        // (0,1,0): base=1000, local_a=5, local_b=12, inner_val=1012
        assert compute(0, 1, 0) == 1012;
        // (0,1,1): base=1000, local_a=5, local_b=12, inner_val=1013
        assert compute(0, 1, 1) == 1013;
        // (1,0,0): base=1000, local_a=16, local_b=36, inner_val=1036
        assert compute(1, 0, 0) == 1036;
        // (1,0,1): base=1000, local_a=16, local_b=36, inner_val=1037
        assert compute(1, 0, 1) == 1037;
        // (1,1,0): base=1000, local_a=16, local_b=46, inner_val=1046
        assert compute(1, 1, 0) == 1046;
        // (1,1,1): base=1000, local_a=16, local_b=46, inner_val=1047
        assert compute(1, 1, 1) == 1047;
        return;
    }

    fn compute(a, b, c) -> 1 {
        base = 1000;
        var outer_val;
        var mid_val;
        var inner_val;

        match a {
            0 => {
                outer_val = 5;
                var local_a;
                local_a = a + outer_val;  // local_a = 5

                match b {
                    0 => {
                        mid_val = 3;
                        var local_b;
                        local_b = local_a + mid_val;  // local_b = 8

                        match c {
                            0 => {
                                inner_val = base + local_b + c;  // 1000 + 8 + 0 = 1008
                            }
                            1 => {
                                inner_val = base + local_b + c;  // 1000 + 8 + 1 = 1009
                            }
                        }
                    }
                    1 => {
                        mid_val = 7;
                        var local_b;
                        local_b = local_a + mid_val;  // local_b = 12

                        match c {
                            0 => {
                                inner_val = base + local_b + c;  // 1000 + 12 + 0 = 1012
                            }
                            1 => {
                                inner_val = base + local_b + c;  // 1000 + 12 + 1 = 1013
                            }
                        }
                    }
                }
            }
            1 => {
                outer_val = 15;
                var local_a;
                local_a = a + outer_val;  // local_a = 16

                match b {
                    0 => {
                        mid_val = 20;
                        var local_b;
                        local_b = local_a + mid_val;  // local_b = 36

                        match c {
                            0 => {
                                inner_val = base + local_b + c;  // 1000 + 36 + 0 = 1036
                            }
                            1 => {
                                inner_val = base + local_b + c;  // 1000 + 36 + 1 = 1037
                            }
                        }
                    }
                    1 => {
                        mid_val = 30;
                        var local_b;
                        local_b = local_a + mid_val;  // local_b = 46

                        match c {
                            0 => {
                                inner_val = base + local_b + c;  // 1000 + 46 + 0 = 1046
                            }
                            1 => {
                                inner_val = base + local_b + c;  // 1000 + 46 + 1 = 1047
                            }
                        }
                    }
                }
            }
        }

        return inner_val;
    }
    "#;
    compile_and_run(
        &ProgramSource::Raw(program.to_string()),
        (&[], &[]),
        DEFAULT_NO_VEC_RUNTIME_MEMORY,
        false,
    );
}
