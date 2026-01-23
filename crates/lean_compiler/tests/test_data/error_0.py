from snark_lib import *

# Error: imported constant name clash (FOO defined in foo.py)
from misc.bar import *
from misc.foo import *

FOO = 5


def main():
    return
