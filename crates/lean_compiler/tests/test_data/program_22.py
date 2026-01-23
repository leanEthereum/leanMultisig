from snark_lib import *


def main():
    result = level_one(3)
    print(result)
    return


@inline
def level_one(x):
    result = level_two(x)
    return result


@inline
def level_two(y):
    result = level_three(y)
    return result


@inline
def level_three(z):
    return z * z * z
