use lean_compiler::*;
use lean_vm::*;
use p3_symmetric::Permutation;
use utils::{get_poseidon16, get_poseidon24};

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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_decompose_bits() {
    let program = r#"
    const A = 2 ** 30 - 1;
    const B = 2 ** 10 - 1;
    fn main() {
        a = decompose_bits(A, B);
        for i in 0..62  {
            print(a[i]);
        }
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
            } else {
                if i == 1 {
                    arr[i] = 20;
                } else {
                    if i == 2 {
                        arr[i] = 30;
                    } else {
                        i_plus_one = i + 1;
                        arr[i] = i_plus_one;
                    }
                }
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
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_mini_program_3() {
    let program = r#"
    fn main() {
        a = public_input_start / 8;
        b = a + 1;
        c = malloc_vec(2);
        poseidon16(a, b, c);

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
    let mut public_input: [F; 16] = (0..16).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(program, &public_input, &[], false);

    get_poseidon16().permute_mut(&mut public_input);
    let _ = public_input;
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
    let mut public_input: [F; 24] = (0..24).map(F::new).collect::<Vec<F>>().try_into().unwrap();
    compile_and_run(program, &public_input, &[], false);

    get_poseidon24().permute_mut(&mut public_input);
    dbg!(&public_input[16..]);
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
        dot_product(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
    fn assert_vectorized_eq_5(x, y) inline {
        dot_product(x * 8, pointer_to_one_vector * 8, y * 8, 1);
        dot_product(x * 8 + 3, pointer_to_one_vector * 8, y * 8 + 3, 1);
        return;
    }
   "#;
    compile_and_run(program, &[], &[], false);
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
    compile_and_run(program, &[], &[], false);
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
//     compile_and_run(program, &[], &[]);
// }
