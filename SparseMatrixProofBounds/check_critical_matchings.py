"""Enumerate small moving-hole probes and their exact monomial variations."""

from fractions import Fraction
from itertools import permutations
from math import comb, perm


def count_changes(r, gap):
    s = r + gap
    switches = r // gap
    totals = [0] * (r + 1)
    trials = 0
    for columns in permutations(range(s)):
        base = columns[:r]
        holes = columns[r:]
        base_prefix = next((k for k in range(r) if base[k] != k), r)
        for rows in permutations(range(r)):
            seen_missing = set()
            for j in range(switches + 1):
                matching = list(base)
                if j:
                    group = rows[(j - 1) * gap:j * gap]
                    for row, column in zip(group, holes):
                        matching[row] = column
                missing = set(range(s)).difference(matching)
                assert not seen_missing.intersection(missing)
                seen_missing.update(missing)
                prefix = next((k for k in range(r) if matching[k] != k), r)
                for k in range(min(base_prefix, prefix) + 1,
                               max(base_prefix, prefix) + 1):
                    totals[k] += 1
            trials += 1
    for k in range(1, r + 1):
        hit = 1 - Fraction(comb(r - k, gap), comb(r, gap))
        expected = Fraction(2 * switches, perm(s, k)) * hit
        actual = Fraction(totals[k], trials)
        assert actual == expected, (r, gap, k, actual, expected)
        assert actual <= Fraction(4, s)
    return r


if __name__ == "__main__":
    checks = sum(count_changes(r, gap) for r in range(1, 5)
                 for gap in range(1, min(r, 2) + 1))
    print(f"Verified {checks} exact monomial variations and disjoint missing sets.")
