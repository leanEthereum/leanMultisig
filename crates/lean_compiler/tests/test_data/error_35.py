from snark_lib import *

# Error: match_range results are always immutable, cannot use Mut
def main():
    x = 1
    result: Mut = match_range(x, range(0, 3), lambda i: i * 10)
    return
