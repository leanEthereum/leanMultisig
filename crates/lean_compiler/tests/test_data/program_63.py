from snark_lib import *


def main():
    even_sum: Mut = 0
    odd_sum: Mut = 0

    for i in unroll(0, 6):
        remainder = i % 2
        if remainder == 0:
            even_sum = even_sum + i
        else:
            odd_sum = odd_sum + i
    assert even_sum == 6
    assert odd_sum == 9
    return
