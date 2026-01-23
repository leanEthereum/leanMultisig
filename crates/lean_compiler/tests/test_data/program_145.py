from snark_lib import *
# Test for inlined functions with const arguments

ARR = [1, 2, 3, 4, 5]
SIZES = [2, 4, 3, 5]
NESTED_ARR = [[2, 4, 6], [1, 3, 5]]


def main():
    # Test 1: Basic
    result1 = sum_to_n(ARR[2])
    assert result1 == 3

    # Test 2: Inside unroll loop
    total: Mut = 0
    for i in unroll(0, 4):
        total = total + sum_to_n(SIZES[i])
    assert total == 20

    # Test 3: Complex expression as argument
    result3 = sum_to_n(ARR[1] + ARR[2])  # sum_to_n(5) = 0+1+2+3+4 = 10
    assert result3 == 10

    # Test 4: Inline function returning const array value as loop bound
    bound = get_bound(1)  # SIZES[1] = 4
    sum4: Mut = 0
    for j in unroll(0, bound):
        sum4 = sum4 + j
    assert sum4 == 6  # 0+1+2+3 = 6

    # Test 5: Zero iterations edge case
    result5 = sum_to_n(0)
    assert result5 == 0

    # Test 6: Single iteration
    result6 = sum_to_n(1)
    assert result6 == 0  # for i in range(0, 1): acc = 0

    # Test 7: Large count
    result7 = sum_to_n(11)  # 0+1+2+...+10 = 55
    assert result7 == 55

    # Test 8: Multiple independent calls in sequence
    a = sum_to_n(3)  # 0+1+2 = 3
    b = sum_to_n(4)  # 0+1+2+3 = 6
    c = sum_to_n(5)  # 0+1+2+3+4 = 10
    assert a + b + c == 19

    # Test 9: Inline function with multiple loop iterations and arithmetic
    result9 = product_factorial(4)  # 1*2*3*4 = 24
    assert result9 == 24

    # Test 10: Nested const array access
    result10 = sum_to_n(NESTED_ARR[0][1])  # NESTED_ARR[0][1] = 4, sum = 6
    assert result10 == 6

    # Test 11: Different inline functions with same pattern
    for k in unroll(0, 3):
        x = sum_to_n(ARR[k])  # ARR[0]=1, ARR[1]=2, ARR[2]=3
        y = sum_squared(ARR[k])  # 0^2 + 1^2 + ... + (n-1)^2
        print(x)
        print(y)

    # Test 12: Inline call with expression involving loop variable and const
    test12_total: Mut = 0
    for m in unroll(0, 3):
        test12_total = test12_total + sum_to_n(ARR[m] + 1)
    # ARR[0]+1=2 -> sum=1, ARR[1]+1=3 -> sum=3, ARR[2]+1=4 -> sum=6
    assert test12_total == 10

    # Test 13: Const expression as inline argument
    result13 = sum_to_n(2 + 3)  # sum_to_n(5) = 10
    assert result13 == 10

    # Test 14: Inline function with no loop (simple passthrough)
    result14 = double_value(SIZES[2])  # SIZES[2]=3, result=6
    assert result14 == 6

    return


# Product: 1 * 2 * ... * n
@inline
def product_factorial(n):
    acc: Mut = 1
    for i in unroll(1, n + 1):
        acc = acc * i
    return acc


# Sum of squares: 0^2 + 1^2 + ... + (n-1)^2
@inline
def sum_squared(n):
    acc: Mut = 0
    for i in unroll(0, n):
        acc = acc + i * i
    return acc


# Returns element from const array
@inline
def get_bound(idx):
    return SIZES[idx]


# Simple passthrough with arithmetic
@inline
def double_value(x):
    return x * 2


@inline
def sum_to_n(n):
    acc: Mut = 0
    for i in unroll(0, n):
        acc = acc + i
    return acc
