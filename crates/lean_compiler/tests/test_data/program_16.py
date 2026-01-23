from snark_lib import *
def main():
    b = is_one()
    c = b
    return

@inline
def is_one():
    if !!assume_bool(1):
        return 1
    else:
        return 0
