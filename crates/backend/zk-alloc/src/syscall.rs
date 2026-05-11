// Raw syscalls instead of libc wrappers to avoid reentrancy: libc's mmap/madvise
// may internally call malloc, which would deadlock when called from inside
// #[global_allocator].

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
mod imp {
    use std::ptr;

    const SYS_MMAP: usize = 9;
    const SYS_MADVISE: usize = 28;

    const PROT_READ: usize = 1;
    const PROT_WRITE: usize = 2;
    const MAP_PRIVATE: usize = 0x02;
    const MAP_ANONYMOUS: usize = 0x20;
    const MAP_NORESERVE: usize = 0x4000;

    pub const MADV_HUGEPAGE: usize = 14;
    pub const MADV_NOHUGEPAGE: usize = 15;

    #[inline]
    unsafe fn syscall6(nr: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize, a6: usize) -> isize {
        let ret: isize;
        unsafe {
            std::arch::asm!(
                "syscall",
                inlateout("rax") nr as isize => ret,
                in("rdi") a1,
                in("rsi") a2,
                in("rdx") a3,
                in("r10") a4,
                in("r8") a5,
                in("r9") a6,
                lateout("rcx") _,
                lateout("r11") _,
                options(nostack),
            );
        }
        ret
    }

    #[inline]
    unsafe fn syscall3(nr: usize, a1: usize, a2: usize, a3: usize) -> isize {
        let ret: isize;
        unsafe {
            std::arch::asm!(
                "syscall",
                inlateout("rax") nr as isize => ret,
                in("rdi") a1,
                in("rsi") a2,
                in("rdx") a3,
                lateout("rcx") _,
                lateout("r11") _,
                lateout("r10") _,
                options(nostack),
            );
        }
        ret
    }

    #[inline]
    pub unsafe fn mmap_anonymous(size: usize) -> *mut u8 {
        let flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE;
        let ret = unsafe { syscall6(SYS_MMAP, 0, size, PROT_READ | PROT_WRITE, flags, usize::MAX, 0) };
        if ret < 0 { ptr::null_mut() } else { ret as *mut u8 }
    }

    #[inline]
    pub unsafe fn madvise(ptr: *mut u8, size: usize, advice: usize) {
        unsafe { syscall3(SYS_MADVISE, ptr as usize, size, advice) };
    }
}

#[cfg(all(target_os = "linux", target_arch = "aarch64"))]
mod imp {
    use std::ptr;

    const SYS_MMAP: usize = 222;
    const SYS_MADVISE: usize = 233;
    const SYS_SYSINFO: usize = 179;

    const PROT_READ: usize = 1;
    const PROT_WRITE: usize = 2;
    const MAP_PRIVATE: usize = 0x02;
    const MAP_ANONYMOUS: usize = 0x20;
    const MAP_NORESERVE: usize = 0x4000;

    pub const MADV_HUGEPAGE: usize = 14;
    pub const MADV_NOHUGEPAGE: usize = 15;

    #[inline]
    unsafe fn syscall6(nr: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize, a6: usize) -> isize {
        let ret: isize;
        unsafe {
            std::arch::asm!(
                "svc 0",
                in("x8") nr,
                inlateout("x0") a1 as isize => ret,
                in("x1") a2,
                in("x2") a3,
                in("x3") a4,
                in("x4") a5,
                in("x5") a6,
                options(nostack),
            );
        }
        ret
    }

    #[inline]
    unsafe fn syscall3(nr: usize, a1: usize, a2: usize, a3: usize) -> isize {
        let ret: isize;
        unsafe {
            std::arch::asm!(
                "svc 0",
                in("x8") nr,
                inlateout("x0") a1 as isize => ret,
                in("x1") a2,
                in("x2") a3,
                options(nostack),
            );
        }
        ret
    }

    #[inline]
    unsafe fn syscall1(nr: usize, a1: usize) -> isize {
        let ret: isize;
        unsafe {
            std::arch::asm!(
                "svc 0",
                in("x8") nr,
                inlateout("x0") a1 as isize => ret,
                options(nostack),
            );
        }
        ret
    }

    /// Returns the system's total RAM in bytes via the `sysinfo(2)` syscall, or
    /// 0 on failure. Allocation-free: writes the kernel struct into a stack
    /// buffer, no libc / no Vec / no String. Safe to call from inside
    /// `#[global_allocator]` initialisation.
    ///
    /// Layout of `struct sysinfo` on 64-bit Linux (kernel/asm-generic):
    ///   off  0  long uptime
    ///   off  8  ulong loads[3]
    ///   off 32  ulong totalram        <-- the field we want
    ///   off 40  ulong freeram
    ///   ...
    ///   off108  u32   mem_unit        <-- multiplier (always 1 on 64-bit)
    pub unsafe fn total_ram_bytes() -> usize {
        let mut buf = [0u8; 128];
        let ret = unsafe { syscall1(SYS_SYSINFO, buf.as_mut_ptr() as usize) };
        if ret < 0 {
            return 0;
        }
        let totalram =
            u64::from_ne_bytes([buf[32], buf[33], buf[34], buf[35], buf[36], buf[37], buf[38], buf[39]]) as usize;
        let mem_unit = u32::from_ne_bytes([buf[108], buf[109], buf[110], buf[111]]) as usize;
        totalram.saturating_mul(mem_unit.max(1))
    }

    #[inline]
    pub unsafe fn mmap_anonymous(size: usize) -> *mut u8 {
        let flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE;
        let ret = unsafe { syscall6(SYS_MMAP, 0, size, PROT_READ | PROT_WRITE, flags, usize::MAX, 0) };
        if ret < 0 { ptr::null_mut() } else { ret as *mut u8 }
    }

    #[inline]
    pub unsafe fn madvise(ptr: *mut u8, size: usize, advice: usize) {
        unsafe { syscall3(SYS_MADVISE, ptr as usize, size, advice) };
    }
}

#[cfg(not(all(target_os = "linux", any(target_arch = "x86_64", target_arch = "aarch64"))))]
mod imp {
    use std::ptr;

    pub const MADV_HUGEPAGE: usize = 14;
    pub const MADV_NOHUGEPAGE: usize = 15;

    #[inline]
    pub unsafe fn mmap_anonymous(size: usize) -> *mut u8 {
        // MAP_NORESERVE is Linux-only. macOS lazily backs anonymous mappings
        // with physical memory by default, so the large virtual reservation
        // is fine without NORESERVE.
        let prot = libc::PROT_READ | libc::PROT_WRITE;
        let flags = libc::MAP_PRIVATE | libc::MAP_ANON;
        let ret = unsafe { libc::mmap(ptr::null_mut(), size, prot, flags, -1, 0) };
        if ret == libc::MAP_FAILED {
            ptr::null_mut()
        } else {
            ret.cast::<u8>()
        }
    }

    #[inline]
    pub unsafe fn madvise(_ptr: *mut u8, _size: usize, _advice: usize) {
        // The advice values we pass are Linux-specific.
    }
}

#[cfg(not(target_arch = "aarch64"))]
pub use imp::MADV_NOHUGEPAGE;
#[cfg(target_arch = "aarch64")]
pub use imp::{MADV_HUGEPAGE, total_ram_bytes};
pub use imp::{madvise, mmap_anonymous};
