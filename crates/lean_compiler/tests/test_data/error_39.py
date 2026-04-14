from snark_lib import *


# Error: assertion on a chain of function calls must fail at runtime.
def main():
    r = outer()
    assert r == 0
    return


def outer():
    return inner() + 1


def inner():
    return 41
