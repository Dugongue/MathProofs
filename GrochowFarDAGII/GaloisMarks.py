"""Exact finite checks of the subgroup marks and the claimed size bounds."""
from functools import lru_cache
from itertools import permutations, product
from math import prod


def subgroup_data(elements, multiply, identity):
    inverse = {g: next(h for h in elements if multiply(g, h) == identity)
               for g in elements}

    def close(generators):
        found = {identity}
        frontier = [identity]
        while frontier:
            g = frontier.pop()
            for h in generators:
                gh = multiply(g, h)
                if gh not in found:
                    found.add(gh)
                    frontier.append(gh)
        return frozenset(found)

    trivial = frozenset([identity])
    subgroups = [trivial]
    seen = {trivial}
    for subgroup in subgroups:
        for g in elements:
            if g not in subgroup:
                candidate = close((*subgroup, g))
                if candidate not in seen:
                    seen.add(candidate)
                    subgroups.append(candidate)

    @lru_cache(None)
    def mobius(lower, upper):
        if lower == upper:
            return 1
        return -sum(mobius(middle, upper) for middle in subgroups
                    if lower < middle <= upper)

    @lru_cache(None)
    def conjugate(subgroup, g):
        return frozenset(multiply(multiply(inverse[g], j), g) for j in subgroup)

    @lru_cache(None)
    def mark(subgroup, stab):
        count = sum(conjugate(subgroup, g) <= stab for g in elements)
        assert count % len(stab) == 0
        return count // len(stab)

    for upper in subgroups:
        for lower in subgroups:
            lhs = sum(len(stab) * mobius(stab, upper) * mark(lower, stab)
                      for stab in subgroups if stab <= upper)
            rhs = sum(conjugate(lower, g) == upper for g in elements)
            assert lhs == rhs
    return subgroups, mark, mobius


def elementary(prime, rank):
    vectors = tuple(product(range(prime), repeat=rank))

    def add(a, b):
        return tuple((x + y) % prime for x, y in zip(a, b))

    return vectors, add, (0,) * rank


def main():
    identity = (0, 1, 2)
    s3, _, _ = subgroup_data(tuple(permutations(identity)),
                             lambda x, y: tuple(x[i] for i in y), identity)
    assert len(s3) == 6
    print("All 36 mark identities for the nonabelian S3 passed.")
    for prime, max_rank in [(2, 4), (3, 3)]:
        for rank in range(1, max_rank + 1):
            elements, add, identity = elementary(prime, rank)
            subgroups, mark, mobius = subgroup_data(elements, add, identity)
            whole = frozenset(elements)
            coefficients = {}
            for subgroup in subgroups:
                numerator = prime * len(subgroup) * mobius(subgroup, whole)
                assert numerator % len(whole) == 0
                coefficients[subgroup] = numerator // len(whole)
            positive = sum(c * (len(whole) // len(h)) for h, c in coefficients.items() if c > 0)
            negative = sum(-c * (len(whole) // len(h)) for h, c in coefficients.items() if c < 0)
            assert positive == negative == prime * prod(1 + prime**j for j in range(1, rank))
            assert any(abs(c) == 1 for c in coefficients.values())
            print(f"p={prime}, rank={rank}: {len(subgroups)} subgroups, minimal size {positive}.")

    elements, add, identity = elementary(2, 2)
    subgroups, mark, mobius = subgroup_data(elements, add, identity)
    lines = [h for h in subgroups if len(h) == 2]
    codes = {h: tuple(int(i == j) for i in range(3)) for j, h in enumerate(lines)}
    codes[frozenset(elements)] = (0, 1, 2)
    codes[frozenset([identity])] = (0, 0, 0)
    differences = {upper: {stab: len(stab) * mobius(stab, upper)
                           for stab in subgroups if stab <= upper}
                   for upper in subgroups if len(upper) > 1}
    for i in range(3):
        for j in range(3):
            marks = {test: sum((codes[upper][i] - codes[upper][j]) * coefficient * mark(test, stab)
                               for upper, coeffs in differences.items()
                               for stab, coefficient in coeffs.items())
                     for test in subgroups}
            for subgroup in subgroups:
                equal = all(marks[lower] == 0 for lower in subgroups if lower <= subgroup)
                assert equal == (codes[subgroup][i] == codes[subgroup][j])
    print("Three-object pattern with distinct merged pairs on the three lines passed.")


if __name__ == "__main__":
    main()
