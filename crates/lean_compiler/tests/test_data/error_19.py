from snark_lib import *


# Error: vector passed to non-inlined function
def main():
    v = DynArray([1, 2, 3])
    process(v)  # Error: vectors cannot be passed to non-inlined functions
    return


def process(x):
    return
