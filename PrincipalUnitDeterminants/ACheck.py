"""Check quotient-label fingerprints and compatible profiles on small rings."""

from collections import Counter
from itertools import product


def multiply(a, b, depth):
    """Multiply in F_2[t]/(t^depth), represented by coefficient bits."""
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        b >>= 1
    return result & ((1 << depth) - 1)


def units(depth):
    return tuple(range(1, 1 << depth, 2))


def subgroups(depth):
    group = units(depth)
    result = []
    for mask in range(1, 1 << len(group), 2):
        subgroup = frozenset(a for i, a in enumerate(group) if mask >> i & 1)
        if all(multiply(a, b, depth) in subgroup for a, b in product(subgroup, repeat=2)):
            result.append(subgroup)
    return result


def reduce_element(a, depth):
    return a & ((1 << depth) - 1)


def translation_stabilizer(fibres, depth):
    return {
        h for h in fibres
        if all(fibres[b] == fibres[multiply(h, b, depth)] for b in fibres)
    }


def valuation(a, depth):
    reduced = reduce_element(a, depth)
    return (reduced & -reduced).bit_length() - 1 if reduced else depth


def validate_prescribed_profiles():
    maximum = 4
    group = units(maximum)
    depths = tuple(range(1, maximum + 1))
    diagonal_size = 1 + len(depths) * (len(group) - 1)
    profiles_checked = 0
    for profile in product(*(subgroups(j) for j in depths)):
        if not all(
            {reduce_element(a, j) for a in profile[j]} <= profile[j - 1]
            for j in depths[:-1]
        ):
            continue
        diagonals = {a: [] for a in group}
        for j, target_subgroup in zip(depths, profile):
            preimage = {a for a in group if reduce_element(a, j) in target_subgroup}
            cosets = {
                frozenset(multiply(a, b, maximum) for b in preimage)
                for a in group
            }
            for code, coset in enumerate(sorted(cosets, key=min)):
                for a in coset:
                    diagonals[a].extend([1 << (j - 1)] * code)
        for j, target_subgroup in zip(depths, profile):
            fibres = {b: Counter() for b in units(j)}
            for a, diagonal in diagonals.items():
                padded = diagonal + [0] * (diagonal_size - len(diagonal))
                # Sorted valuations classify diagonal matrices over this chain ring.
                signature = tuple(sorted(valuation(entry, j) for entry in padded))
                fibres[reduce_element(a, j)][signature] += 1
            found = translation_stabilizer(fibres, j)
            assert found == target_subgroup, (profile, j, found, target_subgroup)
        profiles_checked += 1
    assert profiles_checked == 22
    print(f"{profiles_checked} compatible subgroup profiles checked in F_2[t]/(t^4).")


def validate_mixed_fibres():
    maximum = 3
    g = 0b011
    ordered = [1]
    for _ in range(3):
        ordered.append(multiply(ordered[-1], g, maximum))
    assert len(set(ordered)) == 4
    colors = {a: int(i < 2) for i, a in enumerate(ordered)}
    expected = ({1}, set(units(2)), {1})
    for j, target_subgroup in enumerate(expected, 1):
        fibres = {b: Counter() for b in units(j)}
        for a, value in colors.items():
            fibres[reduce_element(a, j)][valuation(value, j)] += 1
        assert translation_stabilizer(fibres, j) == target_subgroup
    print("Mixed-payload collisions checked through all three precisions.")


if __name__ == "__main__":
    validate_prescribed_profiles()
    validate_mixed_fibres()
