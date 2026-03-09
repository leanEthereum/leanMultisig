from snark_lib import *
# Comprehensive test for nested inlined function calls
# Tests various scenarios where inline functions are nested within other calls

def main():
    # Test 1: Basic nested inline calls - f(g(h(x)))
    # incr(incr(incr(5))) = 8
    result1 = incr(incr(incr(5)))
    assert result1 == 8

    # Test 2: Nested inline calls as argument to print (builtin)
    # This was the original bug: print(incr(incr(incr(5))))
    print(incr(incr(incr(5))))

    # Test 3: Multiple inline calls in one expression
    # double(3) + triple(2) = 6 + 6 = 12
    result3 = double(3) + triple(2)
    assert result3 == 12

    # Test 4: Nested inline calls in arithmetic expression
    # incr(double(3)) * incr(triple(2)) = 7 * 7 = 49
    result4 = incr(double(3)) * incr(triple(2))
    assert result4 == 49

    # Test 5: Multiple levels of nesting in arithmetic
    # double(incr(triple(2))) + incr(double(incr(1)))
    # = double(incr(6)) + incr(double(2))
    # = double(7) + incr(4)
    # = 14 + 5 = 19
    result5 = double(incr(triple(2))) + incr(double(incr(1)))
    assert result5 == 19

    # Test 6: Inline functions calling other inline functions
    # quad(3) = double(double(3)) = double(6) = 12
    result6 = quad(3)
    assert result6 == 12

    # Test 7: Deeply nested composition
    # quad(incr(double(1))) = quad(incr(2)) = quad(3) = 12
    result7 = quad(incr(double(1)))
    assert result7 == 12

    # Test 8: Multiple inline calls as arguments to non-inline function
    # add_three(incr(1), double(2), triple(1)) = add_three(2, 4, 3) = 9
    result8 = add_three(incr(1), double(2), triple(1))
    assert result8 == 9

    # Test 9: Nested inline call as argument to non-inline function
    # add_three(incr(incr(1)), double(incr(2)), triple(incr(0)))
    # = add_three(3, 6, 3) = 12
    result9 = add_three(incr(incr(1)), double(incr(2)), triple(incr(0)))
    assert result9 == 12

    # Test 10: Print multiple nested inline calls
    print(double(5), triple(5), quad(2))

    # Test 11: Complex expression with multiple nested inline calls
    # (incr(double(2)) + triple(incr(1))) * double(incr(incr(0)))
    # = (incr(4) + triple(2)) * double(2)
    # = (5 + 6) * 4
    # = 44
    result11 = (incr(double(2)) + triple(incr(1))) * double(incr(incr(0)))
    assert result11 == 44

    # Test 12: Inline in unrolled loop
    sum: Mut = 0
    for i in unroll(0, 4):
        sum = sum + incr(i)
    # sum = incr(0) + incr(1) + incr(2) + incr(3) = 1 + 2 + 3 + 4 = 10
    assert sum == 10

    # Test 13: Inline functions in if condition (comparison)
    result13: Imu
    if incr(incr(0)) == 2:
        result13 = 100
    else:
        result13 = 0
    assert result13 == 100

    # Test 14: Nested inline calls in both sides of if condition
    result14: Imu
    if double(3) == triple(2):
        result14 = 1
    else:
        result14 = 0
    # double(3) = 6, triple(2) = 6, so they are equal
    assert result14 == 1

    # Test 15: Inline calls inside if/else branches
    result15: Imu
    if 1 == 1:
        result15 = incr(incr(incr(10)))
    else:
        result15 = 0
    assert result15 == 13

    # Test 16: Multiple nested inline calls in if condition
    result16: Imu
    if incr(double(incr(1))) == 5:
        # incr(1) = 2, double(2) = 4, incr(4) = 5
        result16 = 200
    else:
        result16 = 0
    assert result16 == 200

    # Test 17: Inline call with != comparison
    result17: Imu
    if incr(5) != 5:
        result17 = 300
    else:
        result17 = 0
    assert result17 == 300

    # Test 18: Assertion with inline functions
    assert incr(incr(0)) == 2
    assert double(triple(2)) == 12
    assert quad(incr(1)) == 8

    # Test 19: Debug assertion with inline functions
    debug_assert(incr(5) == 6)
    debug_assert(double(incr(2)) == 6)

    # Test 20: Inline in non-unrolled loop
    arr = Array(4)
    for i in range(0, 4):
        arr[i] = incr(i)
    assert arr[0] == 1
    assert arr[1] == 2
    assert arr[2] == 3
    assert arr[3] == 4

    # Test 21: Nested inline calls in non-unrolled loop
    arr2 = Array(3)
    for i in range(0, 3):
        arr2[i] = double(incr(i))
    # double(incr(0)) = double(1) = 2
    # double(incr(1)) = double(2) = 4
    # double(incr(2)) = double(3) = 6
    assert arr2[0] == 2
    assert arr2[1] == 4
    assert arr2[2] == 6

    # Test 22: Mixing inline and non-inline in complex expression inside loop
    sum23: Mut = 0
    for i in unroll(0, 3):
        sum23 = sum23 + add_three(incr(i), double(i), triple(i))
    # i=0: add_three(1, 0, 0) = 1
    # i=1: add_three(2, 2, 3) = 7
    # i=2: add_three(3, 4, 6) = 13
    # total = 1 + 7 + 13 = 21
    assert sum23 == 21

    # Test 24: Chained else-if with inline conditions
    result24: Imu
    x24 = 5
    if incr(x24) == 4:
        result24 = 1
    elif incr(x24) == 5:
        result24 = 2
    elif incr(x24) == 6:
        result24 = 3
    else:
        result24 = 0
    # incr(5) = 6, so third condition matches
    assert result24 == 3

    # Test 25: Inline call as argument to inline call to non-inline function
    # add_three takes 3 args, but we nest inline calls in each position
    result25 = add_three(quad(1), quad(incr(0)), incr(quad(1)))
    # quad(1) = 4
    # quad(incr(0)) = quad(1) = 4
    # incr(quad(1)) = incr(4) = 5
    # add_three(4, 4, 5) = 13
    assert result25 == 13

    return

# Simple inline function: increment by 1
@inline
def incr(a):
    b = a + 1
    return b

# Inline function: multiply by 2
@inline
def double(x):
    return x * 2

# Inline function: multiply by 3
@inline
def triple(x):
    if x == 78990:
        return 236970
    else:
        y: Mut = x
        two: Imu
        match y - x + 1:
            case 0:
                assert False
            case 1:
                two = 2
        for i in range(0, two):
            y = y + x
        return y

# Inline function that calls another inline function
@inline
def quad(x):
    if x == 78990:
        return 157980
    return double(double(x))

# Non-inline function that takes multiple arguments
def add_three(a, b, c):
    return a + b + c
