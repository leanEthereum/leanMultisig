from snark_lib import *


def main():
    x = 2**20 - 1
    a = Array(31)
    print(a)
    hint_decompose_bits(x, a, 31)
    # Big-endian: a[0] = MSB. x = 2^20 - 1 has its lowest 20 bits set,
    # so a[11..30] == 1 and a[0..10] == 0.
    for i in range(0, 11):
        assert a[i] == 0
    for i in range(11, 31):
        debug_assert(a[i] == 1)
        assert a[i] == 1
    return
