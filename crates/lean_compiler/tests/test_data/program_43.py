from snark_lib import *


def main():
    result = increment_twice(5)
    assert result == 7
    return


def increment_twice(x: Mut):
    x = x + 1
    x = x + 1
    return x
