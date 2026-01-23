from snark_lib import *


# Error: debug_assert(not-equal fails (10 != 10 is false))
def main():
    a = 10
    b = 10
    debug_assert(a != b)
    return
