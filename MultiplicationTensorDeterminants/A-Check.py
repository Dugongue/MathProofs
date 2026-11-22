"""Independently check finite consequences of the determinant-one descent theorem."""

from collections import Counter
from functools import cache
from itertools import combinations, permutations
from math import gcd, prod


@cache
def partitions(total, limit):
    if total == 0:
        return ((),)
    return tuple(
        (d,) + rest
        for d in range(1, min(total, limit) + 1)
        for rest in partitions(total - d, d)
    )


@cache
def power_type(profile, m):
    return tuple(sorted(
        d // gcd(d, m) for d in profile for _ in range(gcd(d, m))
    ))


def factors(n):
    primes = set()
    d = 2
    while d * d <= n:
        if n % d == 0:
            primes.add(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        primes.add(n)
    return primes


def expected_cutoff(schedule, oriented):
    if 1 in schedule:
        return float("inf")
    if oriented and all(d % 2 == 0 for d in schedule):
        return 3 if all(d % 3 == 0 for d in schedule) else 4
    primes = sorted(set().union(*(factors(d) for d in schedule)))
    return min(
        prod(2 * p for p in cover) // 2
        for size in range(1, len(primes) + 1)
        for cover in combinations(primes, size)
        if all(any(d % p == 0 for p in cover) for d in schedule)
    )


def first_collision(schedule, oriented, maximum):
    for dimension in range(1, maximum + 1):
        seen = set()
        for profile in partitions(dimension, dimension):
            key = tuple(power_type(profile, m) for m in schedule)
            if oriented:
                key += (len(profile) % 2,)
            if key in seen:
                return dimension
            seen.add(key)
    return float("inf")


def permutation_for_profile(profile):
    values = []
    for d in profile:
        first = len(values)
        values += list(range(first + 1, first + d)) + [first]
    return tuple(values)


def is_odd(permutation):
    return sum(
        a > b for i, a in enumerate(permutation) for b in permutation[i + 1:]
    ) % 2 == 1


def literal_odd_centralizer(profile, census):
    g = permutation_for_profile(profile)
    return any(all(g[p[i]] == p[g[i]] for i in range(len(g))) for p in census)


def odd_from_profile(profile):
    return any(d % 2 == 0 for d in profile) or len(set(profile)) < len(profile)


def main():
    maximum = 16
    schedules = [(1, 12), (6, 10, 15), (4, 9, 25), (12, 18, 24)]
    schedules += [s for size in (1, 2, 3) for s in combinations(range(2, 13), size)]
    for schedule in schedules:
        for oriented in (False, True):
            predicted = expected_cutoff(schedule, oriented)
            actual = first_collision(schedule, oriented, maximum)
            assert actual == (predicted if predicted <= maximum else float("inf")), (
                schedule, oriented, predicted, actual
            )

    centralizers = 0
    for dimension in range(1, 8):
        odd_permutations = [
            p for p in permutations(range(dimension)) if is_odd(p)
        ]
        for profile in partitions(dimension, dimension):
            centralizers += 1
            assert literal_odd_centralizer(profile, odd_permutations) == odd_from_profile(profile)

    power_checks = 0
    collisions = 0
    for dimension in range(1, maximum + 1):
        for m in range(1, 21):
            fibres = Counter()
            for profile in partitions(dimension, dimension):
                actual = power_type(profile, m)
                split = any(gcd(d, m) > 1 for d in profile)
                if not odd_from_profile(profile):
                    assert odd_from_profile(actual) == split, (profile, m)
                if len(set(actual)) == len(actual):
                    assert not split and actual == tuple(sorted(profile)), (profile, m)
                fibres[actual] += 1
                power_checks += 1
            for actual, multiplicity in fibres.items():
                if multiplicity > 1:
                    assert len(set(actual)) < len(actual), (actual, m)
                    collisions += 1

    print(f"{len(schedules)} schedules, ordinary and orientation-compatible minima through {maximum}")
    print(f"{centralizers} literal permutation centralizers checked through degree 7")
    print(f"{power_checks} profile-power cases and {collisions} nontrivial collision fibres")


if __name__ == "__main__":
    main()
