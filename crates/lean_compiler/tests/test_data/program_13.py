from snark_lib import *


def main():
    for i in range(0, 10):
        for j in range(i, 10):
            for k in range(j, 10):
                sum, prod = compute_sum_and_product(i, j, k)
                if sum == 10:
                    print(i, j, k, prod)
    return


def compute_sum_and_product(a, b, c):
    s1 = a + b
    sum = s1 + c
    p1 = a * b
    product = p1 * c
    return sum, product
