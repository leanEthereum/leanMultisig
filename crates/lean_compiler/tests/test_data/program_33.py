from snark_lib import *


def main():
    a = b()
    b = a()
    assert a + b == 30
    return


def a():
    return 10


def b():
    return 20
