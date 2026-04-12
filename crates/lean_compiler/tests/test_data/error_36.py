from snark_lib import *


# Error: assertion on a function return value must fail at runtime.
# Regression test: dead-store elimination previously dropped the constraint
# because `a` is never read after the assert, making the test spuriously pass.
def main():
    a = one()
    assert a == 2
    return


def one():
    return 1
