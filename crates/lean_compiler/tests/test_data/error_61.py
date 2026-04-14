# Error: `%` is compile-time only; operands must be constants (array assignment path).
def main():
    a = one()
    arr = Array(1)
    arr[0] = a % 2
    assert arr[0] == 1
    return

def one():
    return 1
