// Raw syscalls instead of libc wrappers to avoid reentrancy: libc's mmap/madvise
// may internally call malloc, which would deadlock when called from inside
// #[global_allocator].
use std::ptr;

const SYS_MMAP: usize = 9;
const SYS_MADVISE: usize = 28;

const PROT_READ: usize = 1;
const PROT_WRITE: usize = 2;
const MAP_PRIVATE: usize = 0x02;
const MAP_ANONYMOUS: usize = 0x20;
const MAP_NORESERVE: usize = 0x4000;
const MAP_HUGETLB: usize = 0x40000;

pub const MADV_HUGEPAGE: usize = 14;

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
pub unsafe fn mmap_anonymous(size: usize, hugetlb: bool) -> *mut u8 {
    let flags = MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE | if hugetlb { MAP_HUGETLB } else { 0 };
    let ret = unsafe { syscall6(SYS_MMAP, 0, size, PROT_READ | PROT_WRITE, flags, usize::MAX, 0) };
    if ret < 0 {
        ptr::null_mut()
    } else {
        ret as *mut u8
    }
}

#[inline]
pub unsafe fn madvise(ptr: *mut u8, size: usize, advice: usize) {
    unsafe { syscall3(SYS_MADVISE, ptr as usize, size, advice) };
}
