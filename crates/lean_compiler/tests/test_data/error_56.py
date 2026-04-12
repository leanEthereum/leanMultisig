# Error: unary `log2_ceil` is compile-time only; operand must be a constant.
def main():
    a = one()
    out = log2_ceil(a)
    assert out == 0
    return

def one():
    return 1
