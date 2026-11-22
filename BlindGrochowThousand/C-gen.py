"""Generate 250 split-diagonal tensor contrasts from canonical cubic classes.

The Lean file before the generated marker contains the general proofs. The
generator replaces the examples after that marker and their target list.
"""
from itertools import combinations, combinations_with_replacement
from pathlib import Path


ROOT = Path(__file__).resolve().parent
MARKER = "-- Generated instances follow."
PRIMES = (7, 13, 19, 31, 37, 43, 61, 67, 73, 79)
PER_FIELD = 25


def cubic_representatives(prime):
    exponent = (prime - 1) // 3
    classes = {}
    for weight in range(1, prime):
        classes.setdefault(pow(weight, exponent, prime), weight)
    values = sorted(classes.values())
    assert len(values) == 3 and values[0] == 1
    # Put the two nontrivial classes in multiplication order.
    if pow(values[1] * values[1], exponent, prime) != pow(values[2], exponent, prime):
        raise AssertionError("Expected a cyclic group of three cubic classes")
    return values


def pair_representative(left, right):
    shifts = []
    for shift in range(3):
        lhs = tuple(sorted((i + shift) % 3 for i in left))
        rhs = tuple(sorted((i + shift) % 3 for i in right))
        shifts.append(tuple(sorted((lhs, rhs))))
    return min(shifts)


def cases(prime):
    reps = cubic_representatives(prime)
    exponent = (prime - 1) // 3
    hits = []
    for dimension in range(2, 7):
        profiles = list(combinations_with_replacement(range(3), dimension))
        for left, right in combinations(profiles, 2):
            if (left, right) != pair_representative(left, right):
                continue
            a = tuple(reps[i] for i in left)
            b = tuple(reps[i] for i in right)
            lhs = sum(pow(x, exponent, prime) for x in a) % prime
            rhs = sum(pow(x, exponent, prime) for x in b) % prime
            if lhs != rhs:
                hits.append((a, b))
    # Spread the budget across dimensions without random tie breaks.
    return sorted(hits, key=lambda pair: (len(pair[0]), pair))[:PER_FIELD]


def vector(values):
    return "![" + ", ".join(map(str, values)) + "]"


def main():
    source = ROOT / "C.lean"
    core = source.read_text(encoding="utf-8").split(MARKER, 1)[0]
    blocks = [core + MARKER + "\n\n"]
    targets = []
    for prime in PRIMES:
        blocks.append(f"local instance : Fact (Nat.Prime {prime}) := ⟨by decide⟩\n\n")
        rows = cases(prime)
        assert len(rows) == PER_FIELD
        assert len(set(rows)) == PER_FIELD
        for index, (left, right) in enumerate(rows, start=1):
            name = f"p{prime}_{index:02d}"
            targets.append(f"C1000.{name}")
            a, b = vector(left), vector(right)
            blocks.append(
                f"theorem {name} : Contrast (K := ZMod {prime}) {a} {b} := by\n"
                "  apply contrastOfCubicMoment\n"
                "  all_goals decide\n\n"
            )
    assert len(targets) == 250 and len(set(targets)) == 250
    blocks.append("end C1000\n")
    source.write_text("".join(blocks), encoding="utf-8", newline="\n")
    (ROOT / "C.targets").write_text("\n".join(targets) + "\n", encoding="utf-8", newline="\n")


if __name__ == "__main__":
    main()
