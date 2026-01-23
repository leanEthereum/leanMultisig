from snark_lib import *


def main():
    for x in unroll(0, 3):
        func_match(x)
    for x in unroll(0, 2):
        match x:
            case 0:
                y = 10 * (x + 8)
                z = 10 * y
                print(z)
            case 1:
                y = 10 * x
                z = func_2(y)
                print(z)
    return


@inline
def func_match(x):
    match x:
        case 0:
            print(41)
        case 1:
            y = func_1(x)
            print(y + 1)
        case 2:
            y = 10 * x
            print(y)
    return


def func_1(x):
    return x * x * x * x


@inline
def func_2(x):
    return x * x * x * x * x * x
