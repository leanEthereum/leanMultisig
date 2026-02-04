from snark_lib import *


# Error: match_range with non-continuous ranges (gap between 2 and 5)
def main():
    x = 1
    result = match_range(x, range(0, 2), lambda i: i * 10, range(5, 8), lambda i: i * 100)
    return
