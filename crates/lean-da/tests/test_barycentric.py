from snark_lib import *
from ..zkdsl_implem.barycentric import *


# Public input layout (set by the Rust driver):
#
#   memory[0          .. 2*M)         codeword laid out as evens || odds
#                                     (i.e. a_0, a_2, ..., a_{2M-2}, a_1, a_3, ..., a_{2M-1})
#   memory[2*M        .. 2*M + DIM)   r, a random extension field element
#   memory[2*M + DIM  .. 2*M + 2*DIM) expected = M * P(r),
#                                     i.e. the underlying polynomial evaluated
#                                     at r and scaled by M (since we drop the
#                                     1/M factor of the standard barycentric form).
#
# A correct `barycentric_slices` implementation must satisfy
#
#     sum_j slice_L[j] * evens[j] = expected = sum_j slice_R[j] * odds[j]
#
# We assert both equalities by re-using `expected` as the result location of
# the two length-M dot products: any precompile whose output disagrees with
# the value already stored at the result location triggers a constraint
# failure during execution.
def main():
    pub_mem = 0
    codeword = pub_mem
    r        = pub_mem + 2 * M
    expected = pub_mem + 2 * M + DIM

    slice_L, slice_R = barycentric_slices(r)

    dot_product_be(codeword,     slice_L, expected, M)
    dot_product_be(codeword + M, slice_R, expected, M)
    return
