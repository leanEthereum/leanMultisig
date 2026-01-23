from snark_lib import *
from misc.bar import *
from misc.foo import *


def main():
    x = bar(FOO)
    assert x == 6
    return
