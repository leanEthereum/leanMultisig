from snark_lib import *


def main():
    x = double(3)
    y = quad(x)
    print(y)
    return


@inline
def double(a):
    return a + a


@inline
def quad(b):
    result = double(b)
    return result + result
