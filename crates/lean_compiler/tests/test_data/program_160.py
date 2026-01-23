from snark_lib import *


# Test: local vectors inside non-unrolled loops are allowed
# This just tests that local vector creation and push works inside a loop
def main():
    for i in range(0, 3):
        # Local vector created fresh each iteration - allowed
        v = DynArray([1, 2, 3])
        v.push(4)
        # Use the vector within the same iteration
        assert v[0] == 1
        assert v[3] == 4
        assert len(v) == 4
    return
