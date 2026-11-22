"""Independent finite checks for the extension-degree threshold and its extremizers."""
from collections import Counter
from itertools import combinations
from math import gcd, prod


def partitions(n, upper=None):
    if not n:
        yield ()
        return
    for part in range(min(n, upper or n), 0, -1):
        for rest in partitions(n - part, part):
            yield (part,) + rest


def power_cycles(parts, degree):
    counts = Counter()
    for length in parts:
        pieces = gcd(length, degree)
        counts[length // pieces] += pieces
    return tuple(sorted(counts.items()))


def parity_pair(primes):
    m = prod(primes)
    sides = [[], []]
    for size in range(len(primes) + 1):
        for subset in combinations(primes, size):
            length = prod(subset)
            sides[size % 2].extend([length] * (m // length))
    return tuple(tuple(sorted(side, reverse=True)) for side in sides)


def first_collision(degrees, limit):
    checked = 0
    for dimension in range(1, limit + 1):
        seen = {}
        pairs = []
        for parts in partitions(dimension):
            checked += 1
            signature = tuple(power_cycles(parts, k) for k in degrees)
            group = seen.setdefault(signature, [])
            pairs.extend(frozenset((previous, parts)) for previous in group)
            group.append(parts)
        if pairs:
            return dimension, pairs, checked
    raise AssertionError(f"No collision found up to {limit}")


def test():
    schedules = {
        (4,): (2,),
        (2, 3): (2, 3),
        (2, 5): (2, 5),
        (4, 9): (2, 3),
        (6, 10): (2,),
        (10, 15): (5,),
        (14, 21): (7,),
        (26, 39): (2, 3),
        (6, 10, 15): (2, 3),
        (6, 10, 15, 21): (2, 3),
    }
    total_checked = 0
    for degrees, primes in schedules.items():
        expected_pair = parity_pair(primes)
        expected_dimension = sum(expected_pair[0])
        dimension, pairs, checked = first_collision(degrees, expected_dimension)
        assert dimension == expected_dimension
        assert pairs == [frozenset(expected_pair)]
        total_checked += checked
        print(f"{degrees}: dimension {dimension}, one extremal pair")
    primes = (2, 3, 5)
    left, right = parity_pair(primes)
    assert sum(left) == sum(right) == 120
    for k in range(1, 241):
        assert (power_cycles(left, k) == power_cycles(right, k)) == (gcd(k, 30) > 1)
    print(f"{total_checked} partition-schedule checks; 240 spectrum checks in dimension 120")


if __name__ == "__main__":
    test()
