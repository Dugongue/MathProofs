"""Parse the shared whitespace-delimited prime-field TI benchmark format."""
from math import isqrt, prod


def read_pair(path):
    tokens = list(map(int, path.read_text(encoding="utf-8").split()))
    order, prime = tokens[:2]
    sizes = tokens[2:2 + order]
    if order <= 0 or len(sizes) != order or any(dim <= 0 for dim in sizes):
        raise ValueError("invalid positive format")
    if prime < 2 or any(prime % k == 0 for k in range(2, isqrt(prime) + 1)):
        raise ValueError("GF(p) needs a prime p")
    count = prod(sizes)
    remaining = tokens[2 + order:]
    if len(remaining) != 2 * count:
        raise ValueError("wrong number of coefficients")
    if any(not 0 <= x < prime for x in remaining):
        raise ValueError("coefficient outside GF(p)")
    return prime, sizes, remaining[:count], remaining[count:]
