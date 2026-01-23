from snark_lib import *


def main():
    evens: Mut = 0
    odds: Mut = 0
    all: Mut = 0

    for i in unroll(0, 6):
        all = all + 1
        remainder = i % 2
        if remainder == 0:
            evens = evens + i
        else:
            odds = odds + i

    assert evens == 6
    assert odds == 9
    assert all == 6
    return
