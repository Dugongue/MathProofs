"""Append an even matrix multiplication summand in matrix-unit bases."""

from itertools import product
from math import isqrt


def pad(shape, coefficients):
    """Return the padded shape and sparse coefficients, with zero-based mode indices."""
    if len(shape) != 3 or any(not isinstance(n, int) or n < 0 for n in shape):
        raise ValueError("Expected three nonnegative integer dimensions")
    k = max(4, isqrt(max(shape)) + 1)
    k += k % 2
    result = {}
    for triple, value in coefficients.items():
        if len(triple) != 3 or any(i not in range(n) for i, n in zip(triple, shape)):
            raise ValueError("Coordinate outside input shape")
        if value % 3:
            result[triple] = value % 3
    a, b, c = shape
    for i, j, l in product(range(k), repeat=3):
        result[a+k*i+j, b+k*j+l, c+k*l+i] = 1
    return tuple(n+k*k for n in shape), result
