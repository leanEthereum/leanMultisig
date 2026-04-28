include!(concat!(env!("OUT_DIR"), "/info.rs"));

const _: () = assert!(usize::BITS == 64, "this project requires a 64-bit target (for now)");
