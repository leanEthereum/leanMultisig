from snark_lib import *
from ..utils import *

def main():
    pub_mem = NONRESERVED_PROGRAM_INPUT_START
    n = pub_mem[0]
    expected_log2 = pub_mem[1]
    log2 = log2_ceil_runtime(n)
    assert log2 == expected_log2
    return
