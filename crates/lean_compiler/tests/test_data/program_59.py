from snark_lib import *


def main():
    total: Mut = 0
    for i in unroll(0, 5):
        temp = add_one_pure(i)
        total = total + temp
    assert total == 15
    return


@inline
def add_one_pure(x):
    result = x + 1
    return result
