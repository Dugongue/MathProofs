"""Exact finite controls for the prime-cyclic degree-bound proof."""

from collections import Counter
from itertools import combinations, combinations_with_replacement
from math import prod
from random import Random


def zero_sum_rows(p, support, degree):
    """Enumerate the nonnegative lattice relations through the specified degree."""
    coordinate = {weight: i for i, weight in enumerate(support)}
    for length in range(1, degree + 1):
        for prefix in combinations_with_replacement(support, length - 1):
            last = (-sum(prefix)) % p
            if last not in coordinate or (prefix and last < prefix[-1]):
                continue
            row = [0] * len(support)
            for weight in prefix:
                row[coordinate[weight]] += 1
            row[coordinate[last]] += 1
            yield row


def lattice_index(p, support, degree):
    """Index of the generated lattice, or None if the rank is deficient."""
    dimension = len(support)
    basis = [None] * dimension
    for row in zero_sum_rows(p, support, degree):
        for i in range(dimension):
            while row[i] and basis[i] is not None:
                pivot = basis[i]
                quotient, remainder = divmod(row[i], pivot[i])
                row = [a - quotient * b for a, b in zip(row, pivot)]
                if remainder:
                    basis[i], row = row, pivot
            if row[i]:
                basis[i] = row if row[i] > 0 else [-a for a in row]
                break
        if all(basis) and prod(basis[i][i] for i in range(dimension)) == p:
            # The known full kernel still contains every unprocessed relation.
            return p
    if not all(basis):
        return None
    return prod(basis[i][i] for i in range(dimension))


def degree_bound(p, size):
    half_size = (size + 1) // 2
    return (p + half_size - 1) // half_size


def verify():
    counts = Counter()
    for p in (2, 3, 5, 7, 11, 13, 17):
        for size in range(1, p):
            for support in combinations(range(1, p), size):
                degree = degree_bound(p, size)
                index = lattice_index(p, support, degree)
                if index != p:
                    raise AssertionError((p, support, degree, index))
                counts["exhaustive supports"] += 1

    rng = Random(102)
    for p in (19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61):
        for size in range(3, p):
            support = tuple(sorted(rng.sample(range(1, p), size)))
            degree = degree_bound(p, size)
            index = lattice_index(p, support, degree)
            if index != p:
                raise AssertionError((p, support, degree, index))
            counts["sampled supports"] += 1

    for p in (7, 11, 19, 23, 31, 43, 47, 59):
        size = (p - 1) // 2
        assert degree_bound(p, size) == 4
        for _ in range(30):
            support = tuple(sorted(rng.sample(range(1, p), size)))
            index = lattice_index(p, support, 4)
            if index != p:
                raise AssertionError((p, support, 4, index))
            counts["sampled critical degree-four supports"] += 1

    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 31, 43, 61):
        for size in range(1, p):
            low, high = size // 2, (size + 1) // 2
            support = tuple(sorted(a % p for a in range(-low, high + 1) if a))
            degree = degree_bound(p, size)
            at_bound = lattice_index(p, support, degree)
            below_bound = lattice_index(p, support, degree - 1)
            if at_bound != p or below_bound is not None:
                raise AssertionError((p, support, degree, at_bound, below_bound))
            counts["sharpness controls"] += 1

    for category, count in counts.items():
        print(f"{category} = {count}")


if __name__ == "__main__":
    verify()
