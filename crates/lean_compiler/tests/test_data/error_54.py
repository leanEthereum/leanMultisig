# Error: `%` is compile-time only; operands must be constants.
def main():
    a = one()
    out = a % 2
    assert out == 1
    return

def one():
    return 1