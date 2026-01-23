from snark_lib import *
# Test: Mutable variables with different operations in non-unrolled loop


def main():
    product: Mut = 1
    for i in range(1, 6):
        product *= i
    # 1 * 2 * 3 * 4 * 5 = 120
    assert product == 120
    return
