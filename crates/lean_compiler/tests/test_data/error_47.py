from snark_lib import *


# Error: assertion comparing two distinct function return values must fail at runtime.
def main():
    a = first()
    b = second()
    assert a == b
    return


def first():
    return 11


def second():
    return 22
