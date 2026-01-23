from snark_lib import *


def main():
    for i in unroll(0, 5):
        for j in unroll(i, 2 * i):
            print(i, j)
    return
