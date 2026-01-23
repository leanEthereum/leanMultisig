from snark_lib import *

BIG_ENDIAN = 0
LITTLE_ENDIAN = 1


def main():
    x = 2**20 - 1
    a = Array(31)
    print(a)
    hint_decompose_bits(x, a, 31, LITTLE_ENDIAN)
    for i in range(0, 20):
        debug_assert(a[i] == 1)
        assert a[i] == 1
    for i in range(20, 31):
        assert a[i] == 0
    return
