"""Exhaustively compare actual cycle products against the predicted first dimension."""

from collections import Counter
from functools import cache
from itertools import combinations
from math import gcd, inf, lcm, prod


@cache
def partitions(total, cap):
    if total == 0:
        return ((),)
    return tuple(
        (part,) + tail
        for part in range(1, min(total, cap) + 1)
        for tail in partitions(total - part, part)
    )


def factors(value):
    return {p for p in range(2, value + 1) if value % p == 0
            and all(p % d for d in range(2, p))}


def threshold(markers):
    primes = sorted(set().union(*(factors(m) for m in markers)))
    return min((prod(2 * p for p in subset) // 2
                for size in range(1, len(primes) + 1)
                for subset in combinations(primes, size)
                if all(any(m % p == 0 for p in subset) for m in markers)), default=inf)


def product_key(partition, markers):
    counts = Counter()
    for d in partition:
        for m in markers:
            counts[lcm(d, m)] += gcd(d, m)
    return tuple(sorted(counts.items()))


def has_collision(degree, markers):
    partitions_at_degree = partitions(degree, degree)
    keys = {product_key(part, markers) for part in partitions_at_degree}
    return len(keys) < len(partitions_at_degree)


def main():
    profiles = {ms for size in (1, 2, 3) for ms in combinations(range(1, 11), size)}
    profiles.update({(6, 10, 15), (2, 2, 3), (4, 9, 25), (7, 11, 13)})
    comparisons = 0
    for markers in sorted(profiles):
        predicted = threshold(markers)
        for degree in range(1, 17):
            assert has_collision(degree, markers) == (degree >= predicted), (degree, markers)
            comparisons += 1

    # Independent explicit side-120 witness for the hitting set {2, 3, 5}.
    positive = (30,) + (2,) * 15 + (3,) * 10 + (5,) * 6
    negative = (1,) * 30 + (6,) * 5 + (10,) * 3 + (15,) * 2
    assert sum(positive) == sum(negative) == 120 and positive != negative
    assert product_key(positive, (4, 9, 25)) == product_key(negative, (4, 9, 25))
    print(f"{len(profiles)} marker profiles; {comparisons} complete degree comparisons "
          "through 16; explicit degree-120 product collision verified.")


if __name__ == "__main__":
    main()
