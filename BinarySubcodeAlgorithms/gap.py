"""Exact binary subcode counts and witnesses via column types and subset covers.

solve(r, source, target) takes iterables of generator rows encoded as r-bit
integers, least-significant bit first. It returns (count, pi), where pi[i] is
the target position of source coordinate i, or None when the count is zero.
Run this file directly for exhaustive small-length verification.
"""

from collections import defaultdict
from itertools import permutations, product
from math import factorial, prod


def canonical_basis(r, vectors):
    """Return a reduced binary row basis, with the highest set bit as pivot."""
    pivots = {}
    for row in vectors:
        if row < 0 or row >> r:
            raise ValueError("A row is outside the binary ambient space")
        for p in sorted(pivots, reverse=True):
            if row >> p & 1:
                row ^= pivots[p]
        if row:
            p = row.bit_length() - 1
            for q in pivots:
                if pivots[q] >> p & 1:
                    pivots[q] ^= row
            pivots[p] = row
    return tuple(pivots[p] for p in sorted(pivots))


def check_basis(r, code_basis):
    pivots = {word.bit_length() - 1 for word in code_basis}
    return tuple((1 << j) | sum(1 << (word.bit_length() - 1)
                                for word in code_basis if word >> j & 1)
                 for j in range(r) if j not in pivots)


def columns(r, rows):
    return [sum((word >> j & 1) << i for i, word in enumerate(rows)) for j in range(r)]


def reduce_column(value, echelon):
    """Track the original column combination while reducing a column."""
    coefficients = 0
    for pivot in sorted(echelon, reverse=True):
        if value >> pivot & 1:
            vector, mask = echelon[pivot]
            value ^= vector
            coefficients ^= mask
    return value, coefficients


def solve(r, source, target):
    if r < 0:
        raise ValueError("The length must be nonnegative")
    a, b = canonical_basis(r, source), canonical_basis(r, target)
    if len(a) > len(b):
        return 0, None
    if not r:
        return 1, ()
    checks = columns(r, check_basis(r, b))
    type_indices = defaultdict(list)
    affine_bit = 1 << len(a)
    for j, value in enumerate(columns(r, a)):
        type_indices[value | affine_bit].append(j)
    types = list(type_indices)
    sizes = [len(type_indices[v]) for v in types]
    length = 1 << r
    weights = [mask.bit_count() for mask in range(length)]
    syndromes = [0] * length
    possible = defaultdict(set)
    for mask in range(1, length):
        bit = mask & -mask
        syndromes[mask] = syndromes[mask ^ bit] ^ checks[bit.bit_length() - 1]
        possible[weights[mask]].add(syndromes[mask])

    # Keep expensive variables as pivot columns of the augmented type matrix.
    echelon = {}
    free = []
    expansion = {}
    for i in sorted(range(len(types)), key=lambda j: -len(possible[sizes[j]])):
        v, coeffs = reduce_column(types[i], echelon)
        if v:
            echelon[v.bit_length() - 1] = (v, coeffs ^ (1 << i))
        else:
            free.append(i)
            expansion[i] = coeffs
    remainder, affine_pivots = reduce_column(affine_bit, echelon)
    total_syndrome = syndromes[-1]
    if remainder and total_syndrome:
        return 0, None

    def covers(values, forced):
        reserved = sum(forced)  # the masks are disjoint
        point_products = [1] * length
        for i, value in enumerate(values):
            need = forced[i]
            avoid = reserved ^ need
            zeta = [int(weights[x] == sizes[i] and syndromes[x] == value and
                        x & need == need and not x & avoid) for x in range(length)]
            for j in range(r):
                bit = 1 << j
                for start in range(0, length, 2 * bit):
                    for x in range(start + bit, start + 2 * bit):
                        zeta[x] += zeta[x - bit]
            point_products = [a * b for a, b in zip(point_products, zeta)]
        return sum(v if (r - weights[x]) % 2 == 0 else -v
                   for x, v in enumerate(point_products))

    empty = [0] * len(types)
    assignment_count = 0
    feasible_list = None
    for choices in product(*(sorted(possible[sizes[i]]) for i in free)):
        values = [total_syndrome if affine_pivots >> i & 1 else 0 for i in range(len(types))]
        for i, choice in zip(free, choices):
            values[i] = choice
            mask = expansion[i]
            while mask:
                bit = mask & -mask
                values[bit.bit_length() - 1] ^= choice
                mask ^= bit
        if any(v not in possible[m] for v, m in zip(values, sizes)):
            continue
        ways = covers(values, empty)
        if ways and feasible_list is None:
            feasible_list = values
        assignment_count += ways
    if feasible_list is None:
        return 0, None

    forced = empty[:]
    for position in range(r):
        bit = 1 << position
        for i in range(len(types)):
            if forced[i].bit_count() == sizes[i]:
                continue
            forced[i] |= bit
            if covers(feasible_list, forced):
                break
            forced[i] ^= bit
        else:
            raise ArithmeticError("No extension of a positive cover count")
    pi = [0] * r
    for i, value in enumerate(types):
        targets = (j for j in range(r) if forced[i] >> j & 1)
        for src, dst in zip(type_indices[value], targets):
            pi[src] = dst
    return assignment_count * prod(factorial(m) for m in sizes), tuple(pi)


def verify():
    """Compare counts against explicit codeword sets and coordinate permutations."""
    total = 0
    for n in range(5):
        spaces = {frozenset({0})}
        for vector in range(1, 1 << n):
            spaces.update([space | {x ^ vector for x in space} for space in spaces])
        bases = {space: canonical_basis(n, sorted(space)) for space in spaces}
        perms = list(permutations(range(n)))
        for src in spaces:
            images = {}
            for pi in perms:
                images[pi] = {sum((1 << pi[i]) for i in range(n) if v >> i & 1)
                              for v in src}
            for dst in spaces:
                actual = {pi for pi, image in images.items() if image <= dst}
                count, witness = solve(n, bases[src], bases[dst])
                assert count == len(actual)
                assert (witness in actual) if count else (witness is None)
                total += 1
    return total


if __name__ == "__main__":
    print(f"Verified exact counts and witnesses for {verify()} code pairs of lengths 0 to 4.")
