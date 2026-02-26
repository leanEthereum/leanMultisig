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


# unroll(a, b) returns range(a, b) for Python execution
def unroll(a: int, b: int):
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


# Built-in constants
ZERO_VEC_PTR = 0
SAMPLING_DOMAIN_SEPARATOR_PTR = 16
ONE_EF_PTR = 24
POSEIDON_16_NULL_HASH_PTR = 29
REPEATED_ONES_PTR = 37
NUM_REPEATED_ONES_IN_RESERVED_MEMORY = 16
EQ_MLE_COEFFS_PTR = 53
NONRESERVED_PROGRAM_INPUT_START = 55


def poseidon16(left, right, output, mode):
    _ = left, right, output, mode


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


def hint_decompose_16(a, lo, hi):
    _ = a, lo, hi


def hint_less_than(a, b, result_ptr):
    _ = a, b, result_ptr


def log2_ceil(x: int) -> int:
    assert x > 0
    return math.ceil(math.log2(x))


def div_ceil(a: int, b: int) -> int:
    return (a + b - 1) // b


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

def hint_private_input_start(priv_start):
    _ = priv_start

def hint_decompose_bits_xmss(*args):
    _ = args

def hint_log2_ceil(n):
    return log2_ceil(n)

def hint_xmss(buff):
    _ = buff

def hint_merkle(buff, n):
    _ = buff
    _ = n