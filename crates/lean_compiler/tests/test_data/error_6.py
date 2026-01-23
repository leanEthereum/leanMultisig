from snark_lib import *

# Error: imported function name clash (bar defined in bar.py)
from misc.bar import *
from misc.foo import *


def bar():
    return


def main():
    return
