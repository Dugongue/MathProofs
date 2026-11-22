"""Exhaustive dense finite-field control in dimension (2,2,2), over F_2."""
from functools import cache
from itertools import product
from three_vertex import three_vertex_margin, principal_from_maximizer, dot
from control import ARCS, primal

# A subspace is the bit set of its vectors; the five subspaces of F_2^2.
SPACES = (1, 3, 5, 9, 15)
BASES = tuple((u, v) for u in (1, 2, 3) for v in (1, 2, 3) if u != v)
FULL = (15, 15, 15)


def dim(subspace):
    return subspace.bit_count().bit_length()-1


def apply(matrix, x):
    return ((matrix & 3) if x & 1 else 0) ^ ((matrix >> 2) if x & 2 else 0)


@cache
def maps_into(matrix, u, v):
    return all(v >> apply(matrix, x) & 1 for x in range(4) if u >> x & 1)


def principal_routine(first, second):
    possible = [U for U in product(SPACES, repeat=3)
                if all(maps_into(M, U[0], U[1]) for M in first)
                and all(maps_into(M, U[1], U[2]) for M in second)]

    def maximize(theta):
        U = max(possible, key=lambda step: dot(tuple(map(dim, step)), theta))
        return tuple(map(dim, U)), U

    return principal_from_maximizer((2, 2, 2), (1, 1, 1), FULL, maximize)


@cache
def mask(matrix, source, target):
    target_vectors = (0, target[0], target[1], target[0] ^ target[1])
    support = 0
    for i, x in enumerate(source):
        coords = target_vectors.index(apply(matrix, x))
        for j in range(2):
            support |= ((coords >> j) & 1) << (2*i+j)
    return support


@cache
def fixed_basis_value(support):
    return primal(tuple(edge for i, edge in enumerate(ARCS) if support >> i & 1))


def all_bases(first, second):
    values = []
    for left, middle, right in product(BASES, repeat=3):
        lo = hi = 0
        for a in first:
            lo |= mask(a, left, middle)
        for b in second:
            hi |= mask(b, middle, right)
        values.append(fixed_basis_value(lo | hi << 4))
    return max(values)


def check_flag(first, second, result):
    if not result.squared:
        return
    weights = [[], [], []]
    for U, block_weights in result.weighted_steps:
        for i, (u, w) in enumerate(zip(U, block_weights)):
            if not weights[i] or u != weights[i][-1][0]:
                weights[i].append((u, w))
    weight_of = [{} for _ in range(3)]
    for i, grades in enumerate(weights):
        trace = square = 0
        previous = 1
        for u, w in grades:
            multiplicity = dim(u)-dim(previous)
            trace += multiplicity*w
            square += multiplicity*w*w
            for x in (1, 2, 3):
                if (u & ~previous) >> x & 1:
                    weight_of[i][x] = w
            previous = u
        assert trace == 0 and previous == 15
        weights[i] = square
    assert result.squared*sum(weights) == 1
    exponents = []
    for v, matrices in enumerate((first, second)):
        for a in matrices:
            for x in (1, 2, 3):
                y = apply(a, x)
                if y:
                    exponents.append(weight_of[v+1][y]-weight_of[v][x])
    assert min(exponents) == 1


if __name__ == "__main__":
    # The additional pairs use two parallel arrows on each leg.
    cases = [((a,), (b,)) for a, b in product(range(16), repeat=2) if a or b]
    cases += [((a, (7*a+3) % 16), (b, (11*b+5) % 16))
              for a, b in product(range(16), repeat=2)]
    positive = 0
    max_calls = 0
    for first, second in cases:
        result = three_vertex_margin((2, 2, 2), (0, 1, 2), principal_routine(first, second))
        assert result.squared == all_bases(first, second), (first, second, result)
        check_flag(first, second, result)
        positive += bool(result.squared)
        max_calls = max(max_calls, result.queries)
    print(f"{len(cases)} finite-field agreements from {216*len(cases)} adapted-basis tuples; "
          f"{positive} positive flags checked, maximum {max_calls} price queries.")
