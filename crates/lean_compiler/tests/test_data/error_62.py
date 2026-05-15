from snark_lib import *


# Error: an @inline function cannot have an early / conditional `return`.
def main():
    x = pick(1)
    assert x == 10
    return


@inline
def pick(flag):
    if flag == one():
        return 10
    return 20

def one():
    return 1