from snark_lib import *


def main():
    sum: Mut = 0
    for i in unroll(0, 5):
        sum = sum + i
    assert sum == 10
    return
