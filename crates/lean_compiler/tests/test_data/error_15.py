from snark_lib import *


def main():
    a = 5
    b = 10
    a = swap(a, b) + 11
    return


@inline
def swap(a, b):
    return b, a
