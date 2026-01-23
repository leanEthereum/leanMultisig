from snark_lib import *


def main():
    fibonacci(0, 1, 0, 30)
    return


def fibonacci(a, b, i, n):
    if i == n:
        print(a)
        return
    fibonacci(b, a + b, i + 1, n)
    return
