from snark_lib import *


# Error: debug_assert(less-than fails (30 < 20 is false))
def main():
    a = 30
    b = 20
    debug_assert(a < b)
    return
