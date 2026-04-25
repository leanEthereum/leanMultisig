from snark_lib import *


# Error: assertion on an @inline function return must fail at runtime.
def main():
    a = inl()
    assert a == 55
    return


@inline
def inl():
    return 5
