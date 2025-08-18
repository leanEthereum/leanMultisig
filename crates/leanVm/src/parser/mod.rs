use pest_derive::Parser;

use crate::{bytecode::precompiles::PRECOMPILES, lang::Program};

pub mod error;
pub use error::*;
pub mod utils;
pub(crate) use utils::*;
pub mod program;
pub use program::*;
pub mod function;
pub(crate) use function::*;
pub mod statement;
pub(crate) use statement::*;
pub mod condition;
pub(crate) use condition::*;
pub mod expression;
pub(crate) use expression::*;

#[derive(Parser, Debug)]
#[grammar = "grammar.pest"]
pub struct LangParser;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser() {
        let program = r"

// This is a comment

const A = 10000;
const B = 20000;
// Another comment

fn main() {
// this a comment

    c = a + b;
    assert c == d;
    if c != b { // this a comment
        d = 1;
        e = 9;
        f = d * ((a - b) + ((h / 1) + d));
    } else {
        f = 8;
    }
    assert f != g;
    oo = memory[B];
    x = 8;
    y = 9;
    uuu = y[9];
    vvv = y[uuu];

    gh = memory[7];
    hh = memory[gh];

    print(hh);

    xx= poseidon16(x, y);
    xxx = poseidon24(7, b);

    k = public_input_start;

    for i in a..(b + 9) * ( 7 - 7 ) {
        assert i != d;
    }

    for i in a..(b + 9) * ( 7 - 7 ) unroll {
        assert i != d;
    }

    i, j, k = my_function1(b, b, a);
}

fn my_function1(a, const b, c) -> 2 {
    d = a + b;
    e = b + c;
    if e == e {
        return 0, 0;
    }
    if d != e {
        return d, e;
    } else {
        return e, d;
    }
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }

    #[test]
    fn test_const_parameters() {
        let program = r"
fn test_func(const a, b, const c) -> 1 {
    d = a + b + c;
    return d;
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }

    #[test]
    fn test_exponent_operation() {
        let program = r"
fn test_exp() -> 1 {
    a = 2 ** 3;
    b = x ** y ** z;  // Should parse as x ** (y ** z)
    c = (a + b) ** 2;
    d = a ** 2 * b;   // Should parse as (a ** 2) * b
    return a;
}
    ";

        let parsed = parse_program(program).unwrap();
        println!("{parsed}");
    }
}
