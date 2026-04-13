from snark_lib import *


# Error: when earlier asserts pass, a later wrong assert on a function return
# must still fail. Tests that the constraint is not dropped even when the
# variable appears "used" by prior asserts (these reads happen before the
# discarded-looking assignment).
def main():
    a = one()
    assert a + 0 == 1
    assert a * 1 == 1
    assert a == 2
    return


def one():
    return 1
