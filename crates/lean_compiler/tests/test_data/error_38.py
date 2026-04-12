from snark_lib import *


# Error: assertion on a simple arithmetic result must fail at runtime.
def main():
    a = compute()
    assert a == 10
    return


def compute():
    x = 3
    y = 4
    return x + y
