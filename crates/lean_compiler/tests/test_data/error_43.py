from snark_lib import *


# Error: assertion inside an if-branch must fail at runtime when the branch is taken.
def main():
    cond = public_one()
    if cond == 1:
        a = work()
        assert a == 500
    return


def public_one():
    return 1


def work():
    return 7
