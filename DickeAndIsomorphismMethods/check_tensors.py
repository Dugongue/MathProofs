#!/usr/bin/env python3
"""Check the fixed-weight Dicke collision inequalities using exact integers."""

from itertools import combinations
from math import comb


def choose(n, j):
    return comb(n, j) if 0 <= j <= n else 0


def subspace_histograms(d, r):
    """Enumerate RREF matrices, grouped by their even-parity word histogram."""
    ambient = (1 << d) - 1
    bits_per_count = d + 1
    digit_mask = (1 << bits_per_count) - 1
    word_weights = [x.bit_count() + (x.bit_count() % 2) for x in range(ambient + 1)]
    digits = [1 << (bits_per_count * (w // 2)) for w in word_weights]
    histogram_codes = set()
    visited = 0
    for columns in combinations(range(d), r):
        pivots = [1 << j for j in columns]
        free_columns = ambient ^ sum(pivots)
        rows = []
        for pivot in pivots:
            mask = free_columns & ~(2 * pivot - 1)
            options = []
            free = mask
            while True:
                options.append(pivot | free)
                if free == 0:
                    break
                free = (free - 1) & mask
            rows.append(options)

        def enumerate_rows(i, span):
            nonlocal visited
            if i == r:
                histogram_codes.add(sum(digits[word] for word in span))
                visited += 1
                return
            for row in rows[i]:
                enumerate_rows(i + 1, span + [word ^ row for word in span])

        enumerate_rows(0, [0])

    def decode(code):
        return tuple(
            (code >> (bits_per_count * j)) & digit_mask
            for j in range((d + 1) // 2 + 1)
        )

    return visited, [decode(code) for code in histogram_codes]


def gaussian_binomial(d, r):
    numerator = denominator = 1
    for i in range(r):
        numerator *= (1 << d) - (1 << i)
        denominator *= (1 << r) - (1 << i)
    return numerator // denominator


def pair_count(n, j, histogram):
    return sum(
        count * choose(2 * h, h) * choose(n - 2 * h, j - h)
        for h, count in enumerate(histogram)
    )


def reweighted_pair_count(n, s, j):
    """Return 2**j times the partition function with t = 1/2."""
    return sum(
        choose(s, h) ** 2 * choose(n - s, j - h) * (1 << (j - h))
        for h in range(j + 1)
    )


def verify_binary(k):
    n, d = k - 1, k - 2
    spaces = histograms = reweighted = 0
    for r in range(1, d + 1):
        visited, census = subspace_histograms(d, r)
        assert visited == gaussian_binomial(d, r)
        spaces += visited
        histograms += len(census)
        for m in range(2, k // 2 + 1):
            a, b = choose(n, m - 1), choose(n, m)
            target = (a**m * b ** (k - m)) ** (d + r)
            for histogram in census:
                c1 = pair_count(n, m - 1, histogram)
                c0 = pair_count(n, m, histogram)
                if c1 ** (m * d) * c0 ** ((k - m) * d) <= target:
                    continue
                s = r + 1
                total_weight = sum(2 * h * count for h, count in enumerate(histogram))
                assert total_weight == s * (1 << (r - 1)), (k, r, m, histogram)
                z1 = reweighted_pair_count(n, s, m - 1)
                z0 = reweighted_pair_count(n, s, m)
                # Divide by 2**(m*d*(n-s)); this clears denominators of t = 1/2.
                assert z1 ** (m * d) * z0 ** ((k - m) * d) <= target << (m * d * (n - s)), (
                    k, r, m, histogram
                )
                reweighted += 1
    print(f"k={k}: {spaces} nonzero subspaces, {histograms} histograms by rank, "
          f"{reweighted} reweighted histogram tests", flush=True)



def positive_partitions(total, length, maximum=None):
    if length == 0:
        if total == 0:
            yield ()
        return
    if maximum is None:
        maximum = total
    for part in range(1, min(maximum, total - length + 1) + 1):
        for rest in positive_partitions(total - part, length - 1, part):
            yield (part,) + rest


def multinomial(parts):
    result = 1
    left = sum(parts)
    for part in parts:
        result *= comb(left, part)
        left -= part
    return result


def ternary_pair_counts(parts, d, add, negate):
    remaining = list(parts)
    powers = [3**j for j in range(d)]
    support = []

    def enumerate_words(i, encoded):
        if i == d:
            # The unique unused symbol is fixed by the prescribed type.
            support.append(encoded)
            return
        for color in range(3):
            if remaining[color]:
                remaining[color] -= 1
                enumerate_words(i + 1, encoded + color * powers[i])
                remaining[color] += 1

    enumerate_words(0, 0)
    counts = [0] * (3**d)
    for x in support:
        row = add[x]
        for y in support:
            counts[row[negate[y]]] += 1
    return counts


def reweighted_ternary_count(parts, s):
    common, rare1, rare2 = parts
    result = 0
    for h1 in range(rare1 + 1):
        for h2 in range(rare2 + 1):
            h0 = s - h1 - h2
            if not 0 <= h0 <= common:
                continue
            inside = multinomial((h0, h1, h2))
            outside = multinomial((common - h0, rare1 - h1, rare2 - h2))
            result += inside * inside * outside * (1 << (rare1 + rare2 - h1 - h2))
    return result


def verify_ternary(k):
    from math import prod

    d, n = k - 2, k - 1
    add = [[0]]
    for i in range(d):
        width = 3**i
        add = [
            [x + ((a + b) % 3) * width for b in range(3) for x in row]
            for a in range(3)
            for row in add
        ]
    digits = [tuple((a // 3**j) % 3 for j in range(d)) for a in range(3**d)]
    negate = [a.index(0) for a in add]
    double = [row[a] for a, row in enumerate(add)]
    masks = [
        sum(1 << j for j, digit in enumerate(row) if digit)
        | ((1 << d) if sum(row) % 3 else 0)
        for row in digits
    ]

    instances = []
    for parts in positive_partitions(k, 3):
        conditional = [
            tuple(value - (i == b) for i, value in enumerate(parts))
            for b in range(3)
        ]
        frequencies = [ternary_pair_counts(t, d, add, negate) for t in conditional]
        instances.append((parts, conditional, frequencies))

    visited = reweighted = 0
    for r in range(1, d + 1):
        seen = [set() for _ in instances]
        targets = [
            prod(multinomial(t) ** p for t, p in zip(conditional, parts)) ** (d + r)
            for parts, conditional, _ in instances
        ]
        rank_start = visited
        for pivots in combinations(range(d), r):
            rows = [
                [
                    a for a, row in enumerate(digits)
                    if row[pivot] == 1
                    and all(row[j] == 0 for j in range(pivot))
                    and all(row[j] == 0 for j in pivots if j != pivot)
                ]
                for pivot in pivots
            ]

            def enumerate_rows(i, span, mask):
                nonlocal visited, reweighted
                if i != r:
                    for row in rows[i]:
                        next_span = (
                            span + [add[row][word] for word in span]
                            + [add[double[row]][word] for word in span]
                        )
                        enumerate_rows(i + 1, next_span, mask | masks[row])
                    return
                visited += 1
                s = mask.bit_count()
                for j, (parts, conditional, frequencies) in enumerate(instances):
                    counts = tuple(sum(freq[word] for word in span) for freq in frequencies)
                    if (counts, s) in seen[j]:
                        continue
                    seen[j].add((counts, s))
                    exponents = tuple(p * d for p in parts)
                    if prod(c**e for c, e in zip(counts, exponents)) <= targets[j]:
                        continue
                    assert s == r + 1, (k, r, parts, counts, s)
                    weighted = [reweighted_ternary_count(t, s) for t in conditional]
                    shift = d * (parts[1] + parts[2]) * (n - s)
                    assert prod(c**e for c, e in zip(weighted, exponents)) <= targets[j] << shift, (
                        k, r, parts, counts, s
                    )
                    reweighted += 1

            enumerate_rows(0, [0], 0)

        number = prod(3**d - 3**i for i in range(r)) // prod(3**r - 3**i for i in range(r))
        assert visited - rank_start == number
    print(f"k={k}: {visited} ternary subspaces, {len(instances)} types, "
          f"{reweighted} reweighted tests", flush=True)


if __name__ == "__main__":
    for k in range(4, 9):
        verify_ternary(k)
    for k in range(5, 12):
        verify_binary(k)
