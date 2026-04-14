from snark_lib import *


# Error: assertion on a multi-return function value must fail at runtime.
def main():
    a, b = pair()
    assert b == 99
    return


def pair():
    return 3, 4
