from snark_lib import *


def main():
    y = compute_value(3)
    print(y)
    return


def compute_value(n: Const):
    result = complex_computation(n, 5)
    return result


def complex_computation(a: Const, b: Const):
    return a * a + b * b
