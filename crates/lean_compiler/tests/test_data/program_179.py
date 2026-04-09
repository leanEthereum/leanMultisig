from snark_lib import *


def main():
    input = Array(5)
    output = Array(5)
    input[0] = 1
    input[4] = 5
    copy_5(input, output)
    assert output[0] == 1
    assert output[4] == 5
    return


@inline
def copy_5(a, b):
    dot_product_ee(a, ONE_EF_PTR, b)
    return
