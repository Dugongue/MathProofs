"""Exact finite controls for the directional-gap theorem over F3."""
from itertools import combinations
import json

G = frozenset(range(8))
E1 = 1
DIAGONAL = 7


def char(w, v):
    return (w & v).bit_count() % 2


def d1(profile):
    return E1 in profile and 0 not in profile


def shift(profile, offset):
    return frozenset(p ^ offset for p in profile)


def subgroups():
    for size in (1, 2, 4, 8):
        for subset in combinations(G, size):
            space = frozenset(subset)
            if 0 in space and all(a ^ b in space for a in space for b in space):
                yield space


def run():
    spaces = tuple(subgroups())
    profiles = {(shift(s, v)) for s in spaces for v in G} | {frozenset()}
    assert len(spaces) == 16 and len(profiles) == 52
    tests = 0
    for profile in profiles:
        pos = []
        misses = []
        for w in G - {0}:
            signs = frozenset(char(w, v) for v in profile)
            diagonal = {DIAGONAL * v for v in signs}
            padded = {a | b for a in signs for b in (0, 2, 4, 6)}
            assert d1(shift(diagonal, E1)) == (0 in signs)
            assert d1(shift(diagonal, E1 ^ DIAGONAL)) == (1 in signs)
            assert d1(padded) == (1 in signs and 0 not in signs)
            assert not profile or d1(padded) == (0 not in signs)
            pos.append(d1(shift(diagonal, E1)))
            misses.append(d1(padded))
            tests += 1
        assert (0 in profile) == (bool(profile) and all(pos))
        assert (0 not in profile) == (not profile or (bool(profile) and any(misses)))

    witness_tests = 0
    for space in spaces:
        for witness in G:
            clauses = [any(char(w, v) for v in space) for w in G if char(w, witness)]
            assert (witness in space) == all(clauses)
            assert d1(shift(space, witness)) == ((witness ^ E1) in space and E1 not in space)
            witness_tests += 1

    for ds in [{0}, {0, 1}]:
        images = {(l ^ d) + 2 * (r ^ d) + 4 * (l ^ r ^ d)
                  for d in ds for l in range(2) for r in range(2)}
        assert images == {v for v in G if char(7, v) in ds}
        assert d1(shift(images, E1)) == (1 not in ds)

    return {"subspaces": len(spaces), "profiles_including_empty": len(profiles),
            "character_profile_checks": tests, "witness_coset_checks": witness_tests,
            "product_unit_sign_cases": 2}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
