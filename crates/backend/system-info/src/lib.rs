include!(concat!(env!("OUT_DIR"), "/info.rs"));

const _: () = assert!(usize::BITS == 64, "this project requires a 64-bit target (for now)");

pub fn peak_rss_bytes() -> u64 {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    unsafe { libc::getrusage(libc::RUSAGE_SELF, &raw mut ru) };
    let max = ru.ru_maxrss as u64;
    // ru_maxrss unit: bytes on macOS, KiB on Linux.
    if cfg!(target_os = "macos") { max } else { max * 1024 }
}
