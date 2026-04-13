from snark_lib import *


# Error: assertion with subtraction-derived value must fail at runtime.
def main():
    a = ten()
    diff = a - 3
    # diff = 7, not 1
    assert diff == 1
    return


def ten():
    return 10
