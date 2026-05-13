//! MRE for compiler inefficiency: redundant copies from Mut variable unification
//! across if-branches. A `Mut` variable updated inside a chain of `if x: ...`
//! statements produces a cascade of pure `m[fp + X] = 0 + m[fp + Y]` copies,
//! because every if/else picks a fresh unified SSA version (`max + 1`).
//!
//! Run: cargo run --release -p lean_compiler --example mre_copies

use lean_compiler::{ProgramSource, compile_program};

fn main() {
    // Inputs come from `hint_witness` so the conditions aren't constant-folded.
    // The chain of `if x: counter = ...` is the pattern that triggers the
    // cascade of unified-version copies in `unify_branch_versions`.
    let source = r#"
def main():
    flags = Array(5)
    hint_witness("flags", flags)
    counter: Mut = 0
    if flags[0] == 1:
        counter = counter + 1
    if flags[1] == 1:
        counter = counter + 2
    if flags[2] == 1:
        counter = counter + 4
    if flags[3] == 1:
        counter = counter + 8
    if flags[4] == 1:
        counter = counter + 16
    print(counter)
    return
"#;

    let bytecode = compile_program(&ProgramSource::Raw(source.to_string()));
    let pretty = bytecode.pretty_print();

    let n_total = bytecode.size();
    let mut n_copies = 0;
    let mut n_panics = 0;
    for line in pretty.lines() {
        let t = line.trim_start();
        if !t.starts_with(char::is_numeric) {
            continue;
        }
        if let Some((_, instr)) = t.split_once(':')
            && instr.contains("= 0 + m[fp + ")
        {
            n_copies += 1;
        }
        if t.contains("1 = 0 x fp + 0") {
            n_panics += 1;
        }
    }

    println!("{pretty}");
    println!("-- summary --");
    println!("total instructions: {n_total}");
    println!("pure copies (`= 0 + m[fp + N]`): {n_copies}");
    println!("panic constraints (`1 = 0 x fp + 0`): {n_panics}");
}
