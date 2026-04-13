from snark_lib import *


# Error: assertion with multiplication-derived value must fail at runtime.
def main():
    a = six()
    prod = a * 7
    # prod = 42, not 0
    assert prod == 0
    return


def six():
    return 6
