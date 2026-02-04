# Test: const argument functions in nested expressions
# Previously crashed with "Function used but not defined"

def main():
    # Nested expression with const-arg function
    three = double(1) + 1
    assert three == 3

    # Multiple nested calls
    ten = double(2) + double(3)
    assert ten == 10

    # Deeper nesting
    result = double(1) * double(2) + double(0)
    assert result == 8
    return

def double(a: Const):
    return a + a
