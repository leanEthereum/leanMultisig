from snark_lib import *


def main():
    match 1:
        case 0:
            y = 90
        case 1:
            y = 10
            z = func_2(y)
    return


@inline
def func_2(x):
    return x * x
