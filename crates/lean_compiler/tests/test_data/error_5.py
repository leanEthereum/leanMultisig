from snark_lib import *


# Error: duplicate function name (a defined twice)
def a():
    return 0


def a():
    return 1


def main():
    a()
    return
