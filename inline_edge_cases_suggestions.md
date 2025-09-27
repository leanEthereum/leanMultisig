# Additional Edge Cases for Inline Return SSA Violations

Based on the analysis of the current test coverage, here are additional edge cases that should be added to `test_compiler.rs`:

## 1. Loop-Related Edge Cases

```rust
#[test]
fn test_inline_returns_in_loops() {
    let program = r#"
        fn main() {
            result = loop_returns(3);
            print(result);
            return;
        }

        fn loop_returns(n) inline -> 1 {
            for i in 0..n {
                if i == 1 {
                    return 100;
                }
            }
            return 200;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_inline_nested_loops_returns() {
    let program = r#"
        fn main() {
            result = nested_loop_returns(2, 2);
            print(result);
            return;
        }

        fn nested_loop_returns(x, y) inline -> 1 {
            for i in 0..x {
                for j in 0..y {
                    if i == j {
                        return 300;
                    }
                }
                if i == 1 {
                    return 400;
                }
            }
            return 500;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 2. Match Statement Edge Cases

```rust
#[test]
fn test_inline_returns_in_match() {
    let program = r#"
        fn main() {
            result1 = match_returns(0);
            result2 = match_returns(1);
            result3 = match_returns(5);
            print(result1);
            print(result2);
            print(result3);
            return;
        }

        fn match_returns(x) inline -> 1 {
            match x {
                0 => {
                    return 100;
                }
                1 => {
                    if x == 1 {
                        return 200;
                    }
                }
                _ => {}
            }
            return 300;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_inline_nested_match_returns() {
    let program = r#"
        fn main() {
            result = nested_match_returns(1, 1);
            print(result);
            return;
        }

        fn nested_match_returns(x, y) inline -> 1 {
            match x {
                1 => {
                    match y {
                        1 => { return 400; }
                        _ => { return 500; }
                    }
                }
                _ => {}
            }
            return 600;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 3. Multiple Return Values Edge Cases

```rust
#[test]
fn test_inline_multiple_return_values_ssa() {
    let program = r#"
        fn main() {
            a, b = multi_return(1);
            print(a);
            print(b);
            return;
        }

        fn multi_return(x) inline -> 2 {
            if x == 0 {
                return 100, 200;
            }
            return 300, 400;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_inline_multiple_returns_complex_ssa() {
    let program = r#"
        fn main() {
            a, b, c = complex_multi_return(2);
            print(a);
            print(b);
            print(c);
            return;
        }

        fn complex_multi_return(x) inline -> 3 {
            if x == 1 {
                if x == 0 {
                    return 100, 200, 300;
                }
                return 400, 500, 600;
            }
            return 700, 800, 900;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 4. Deeply Nested Conditions

```rust
#[test]
fn test_inline_deeply_nested_conditions() {
    let program = r#"
        fn main() {
            result = deeply_nested(2);
            print(result);
            return;
        }

        fn deeply_nested(x) inline -> 1 {
            if x == 1 {
                if x == 2 {
                    if x == 3 {
                        if x == 4 {
                            return 1000;
                        }
                        return 2000;
                    }
                    return 3000;
                }
                return 4000;
            }
            return 5000;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 5. Mixed Control Flow Edge Cases

```rust
#[test]
fn test_inline_mixed_control_flow_ssa() {
    let program = r#"
        fn main() {
            result = mixed_control_flow(1, 2);
            print(result);
            return;
        }

        fn mixed_control_flow(x, y) inline -> 1 {
            if x == 1 {
                for i in 0..y {
                    if i == 1 {
                        return 100;
                    }
                }
                match y {
                    2 => { return 200; }
                    _ => {}
                }
                return 300;
            }
            return 400;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}

#[test]
fn test_inline_complex_fallthrough_patterns() {
    let program = r#"
        fn main() {
            result1 = complex_fallthrough(0);
            result2 = complex_fallthrough(1);
            result3 = complex_fallthrough(2);
            print(result1);
            print(result2);
            print(result3);
            return;
        }

        fn complex_fallthrough(x) inline -> 1 {
            if x == 0 {
                if x == 1 { return 100; }
                if x == 0 { return 200; }
            } else {
                if x == 1 {
                    if x == 2 { return 300; }
                    return 400;
                }
            }
            return 500;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 6. Recursive Inline Edge Cases

```rust
#[test]
fn test_inline_with_inline_calls() {
    let program = r#"
        fn main() {
            result = caller_inline(2);
            print(result);
            return;
        }

        fn caller_inline(x) inline -> 1 {
            if x == 1 {
                return helper_inline(x);
            }
            return helper_inline(x + 1);
        }

        fn helper_inline(y) inline -> 1 {
            if y == 0 {
                return 100;
            }
            return 200;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

## 7. Early Return Optimization Edge Cases

```rust
#[test]
fn test_inline_early_return_optimizable() {
    let program = r#"
        fn main() {
            result = early_return_simple(5);
            print(result);
            return;
        }

        fn early_return_simple(x) inline -> 1 {
            if x > 10 {
                return x * 2;
            }
            if x > 5 {
                return x * 3;
            }
            if x > 0 {
                return x * 4;
            }
            return 0;
        }
    "#;
    compile_and_run(program, &[], &[], false);
}
```

These edge cases cover:
- **Loop interactions** with returns
- **Match statement** non-exhaustive patterns
- **Multiple return values** with SSA violations
- **Deeply nested conditions** (stress testing)
- **Mixed control flow** (loops + match + if)
- **Complex fallthrough patterns**
- **Inline functions calling other inline functions**
- **Early return optimization patterns**

Each test should have a descriptive name that clearly indicates what pattern it's testing.