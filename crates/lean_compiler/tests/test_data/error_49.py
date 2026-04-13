from snark_lib import *


# Error: assertion on a deeply nested call chain must fail at runtime.
def main():
    r = a()
    assert r == 123
    return


def a():
    return b() + 1


def b():
    return c() + 1


def c():
    return d() + 1


def d():
    return 0
