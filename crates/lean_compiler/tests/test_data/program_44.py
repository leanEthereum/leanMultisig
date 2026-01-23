from snark_lib import *
def main():
    a, b: Mut = get_two()
    b = b + 1
    assert a == 10
    assert b == 21
    return

def get_two():
    return 10, 20