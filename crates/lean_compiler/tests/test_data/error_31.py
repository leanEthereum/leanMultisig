from snark_lib import *


# Error: Inconsistent return counts in function
def main():
    x = bad_func(0)
    return


def bad_func(cond):
    if cond == 0:
        return 1
    else:
        return 1, 2
