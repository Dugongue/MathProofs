"""Compare the mixed threshold to characteristic coefficients and actual cycle powers."""
from collections import Counter
from itertools import combinations
from math import gcd, prod
from CountingCheck import factors, partitions


def polynomial(partition, modulus):
    coefficients = [1]
    for d in partition:
        old = coefficients
        coefficients = old + [0] * d
        for i, c in enumerate(old):
            coefficients[i + d] = (coefficients[i + d] - c) % modulus
    return tuple(c % modulus for c in coefficients)


def power(partition, s):
    result = Counter()
    for d in partition:
        g = gcd(s, d)
        result[d // g] += g
    return tuple(sorted(result.items()))


def lattice_key(partition, modulus):
    primes = factors(modulus)
    h = modulus // prod(primes)
    components = []
    for p in sorted(primes):
        counts = Counter()
        for d in partition:
            u = d
            while u % p == 0:
                u //= p
            counts[u] += d // u
        components.append(tuple(sorted(counts.items())))
    components.append(tuple(sorted((d, a % h) for d, a in Counter(partition).items() if a % h)))
    return tuple(components)


def witness(modulus, markers):
    required = factors(modulus)
    candidates = sorted(required.union(*(factors(s) for s in markers)))
    covers = [c for size in range(1, len(candidates) + 1)
              for c in combinations(candidates, size) if required <= set(c)
              and all(any(s % p == 0 for p in c) for s in markers)]
    if not covers:
        return None
    cover = min(covers, key=lambda c: prod(2 * p for p in c))
    h = modulus // prod(required)
    q = prod(cover)
    sides = [[], []]
    for size in range(len(cover) + 1):
        for subset in combinations(cover, size):
            d = prod(subset)
            sides[size % 2].extend([d] * (h * q // d))
    return tuple(tuple(sorted(side, reverse=True)) for side in sides)


def main():
    limit = 24
    cases = [(m, ()) for m in (2,3,4,5,6,8,9,10,12,15,18,30)]
    cases += [(4,(15,21)), (1,(6,10,15)), (6,(5,)), (8,(1,)), (9,(10,14))]
    observations = 0
    for m, markers in cases:
        def key(part):
            return polynomial(part, m), tuple(power(part, s) for s in markers)
        pair = witness(m, markers)
        cutoff = sum(pair[0]) if pair else float("inf")
        if pair:
            assert pair[0] != pair[1] and sum(pair[1]) == cutoff and key(pair[0]) == key(pair[1])
        for n in range(1, limit + 1):
            seen, forward, backward = {}, {}, {}
            first_pairs = []
            for part in partitions(n, n):
                value = key(part)
                equal_on = lattice_key(part, m)
                assert forward.setdefault(value[0], equal_on) == equal_on
                assert backward.setdefault(equal_on, value[0]) == value[0]
                if value in seen:
                    first_pairs.append({part, seen[value]})
                seen[value] = part
                observations += 1
            assert bool(first_pairs) == (n >= cutoff), (m, markers, n)
            if n == cutoff:
                assert first_pairs == [set(pair)], (m, markers, n, first_pairs)
    print(f"{len(cases)} panels, {observations} partition observations through dimension {limit}; "
          "all prime-power equivalences, thresholds, and first pairs in range agree.")


if __name__ == "__main__":
    main()
