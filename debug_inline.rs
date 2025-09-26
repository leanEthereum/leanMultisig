use lean_compiler::*;
use lean_vm::*;

fn main() {
    let program = r#"
        fn main() {
            result = simple(1);
            print(result);
            return;
        }
        fn simple(x) inline -> 1 {
            if x == 0 {
                return 100;
            }
            return 200;
        }
    "#;

    // Parse and simplify to see what's generated
    let (parsed_program, _) = crate::parser::parse_program(program).unwrap();
    let simplified = crate::simplify::simplify_program(parsed_program);

    println!("Simplified program:");
    for (func_name, func) in &simplified.functions {
        println!("  Function: {}", func_name);
        for (i, line) in func.body.iter().enumerate() {
            println!("    Line {}: {:?}", i, line);
        }
    }

    // Now compile
    let (bytecode, _) = compile_program(program);
    println!("\nBytecode:");
    for (i, instruction) in bytecode.instructions.iter().enumerate() {
        println!("  {}: {:?}", i, instruction);
    }
}