# Import this in zkDSL .py files to make them executable as normal Python

import math
from typing import Any

# Type annotations
Mut = Any
Const = Any
Imu = Any


# @inline decorator (does nothing in Python execution)
def inline(fn):
    return fn


def unroll(a: int, b: int):
    return range(a, b)

def parallel_range(a: int, b: int):
    return range(a, b)

# dynamic_unroll(start, end, n_bits) returns range(start, end) for Python execution
def dynamic_unroll(start: int, end: int, n_bits: int):
    _ = n_bits
    return range(start, end)


# Array - simulates write-once memory with pointer arithmetic
class Array:
    def __init__(self, size: int):
        # TODO
        return

    def __getitem__(self, idx):
        # TODO
        return

    def __setitem__(self, idx, value):
        # TODO
        return

    def __add__(self, offset: int):
        # TODO
        return

    def __len__(self):
        # TODO
        return


# DynArray - dynamic array with push/pop (compile-time construct)
class DynArray:
    def __init__(self, initial: list):
        self._data = list(initial)

    def __getitem__(self, idx):
        return self._data[idx]

    def __len__(self):
        return len(self._data)

    def push(self, value):
        self._data.append(value)

    def pop(self):
        self._data.pop()


def poseidon16_compress(left, right, output):
    _ = left, right, output


def poseidon16_compress_half(left, right, output):
    """Poseidon16 compression outputting only the first 4 FE (last 4 unconstrained)."""
    _ = left, right, output


def poseidon16_compress_hardcoded_left_4(left, right, output, offset):
    """Poseidon16 compression where the first 4 FE of the left input are read from
    memory[offset..offset+4] instead of memory[left..left+4]. The last 4 FE of the
    left input still come from memory[left+4..left+8]. `offset` must be a compile-time
    constant expression."""
    _ = left, right, output, offset


def poseidon16_compress_half_hardcoded_left_4(left, right, output, offset):
    """Composition of `poseidon16_compress_half` and `poseidon16_compress_hardcoded_left_4`."""
    _ = left, right, output, offset


def add_be(a, b, result, length=None):
    _ = a, b, result, length


def add_ee(a, b, result, length=None):
    _ = a, b, result, length


def dot_product_be(a, b, result, length=None):
    _ = a, b, result, length


def dot_product_ee(a, b, result, length=None):
    _ = a, b, result, length


def poly_eq_be(a, b, result, length=None):
    _ = a, b, result, length


def poly_eq_ee(a, b, result, length=None):
    _ = a, b, result, length


def hint_decompose_bits(value, bits, n_bits, endian):
    _ = value, bits, n_bits, endian

def hint_less_than(a, b, result_ptr):
    _ = a, b, result_ptr


def log2_ceil(x: int) -> int:
    assert x > 0
    return math.ceil(math.log2(x))


def div_ceil(a: int, b: int) -> int:
    return (a + b - 1) // b

def div_floor(a: int, b: int) -> int:
    return a // b

def next_multiple_of(x: int, n: int) -> int:
    return x + (n - x % n) % n


def saturating_sub(a: int, b: int) -> int:
    return max(0, a - b)


def debug_assert(cond, msg=None):
    if not cond:
        if msg:
            raise AssertionError(msg)
        raise AssertionError()


def match_range(value: int, *args):
    """Match a value against multiple continuous ranges with different lambdas.

    Usage: match_range(value, range(a,b), lambda1, range(b,c), lambda2, ...)
    In zkDSL, this expands to a match statement.
    In Python execution, it finds the matching range and calls the corresponding lambda.
    """
    for i in range(0, len(args), 2):
        rng = args[i]
        fn = args[i + 1]
        if value in rng:
            return fn(value)
    raise AssertionError(f"Value {value} not in any range")


def hint_decompose_bits_xmss(*args):
    _ = args


def hint_decompose_bits_merkle_whir(*args):
    _ = args


def hint_log2_ceil(n):
    return log2_ceil(n)


def hint_read(name, destination):
    """Write the next witness entry for `name` into `destination`."""
    _ = (name, destination)
