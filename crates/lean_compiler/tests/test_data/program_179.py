from snark_lib import *

ONE_EF_PTR = 1  # right after the (empty-public-input) zero-padded cell at memory[0]


def main():
    init_one_ef()
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


@inline
def init_one_ef():
    one_ef = ONE_EF_PTR
    one_ef[0] = 1
    one_ef[1] = 0
    one_ef[2] = 0
    one_ef[3] = 0
    one_ef[4] = 0
    return
