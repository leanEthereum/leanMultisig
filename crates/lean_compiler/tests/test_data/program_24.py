from snark_lib import *


def main():
    a = 10
    b = 20
    debug_assert(a * 2 == b)
    debug_assert(a != b)
    debug_assert(a < b)
    return
