"""Search distinct finite permutation-test panels and generate Lean certificates."""

from collections import Counter
from functools import cache
from itertools import combinations_with_replacement
from math import gcd
from pathlib import Path
from random import Random
import argparse

FAMILIES = ("fixed", "nullity", "hybrid", "extension", "characteristic")
CEILING = 11
SCAN_LIMIT = 10
SEED = 667813


@cache
def partitions(n, limit):
    if not n:
        return ((),)
    return tuple(
        (d,) + rest
        for d in range(1, min(limit, n) + 1)
        for rest in partitions(n - d, d)
    )


@cache
def observe(probe, profile):
    mode, exponent, modulus = probe
    if mode == "fixed":
        count = sum(d for d in profile if exponent % d == 0)
        return count % modulus if modulus else count
    if mode == "nullity":
        count = sum(gcd(d, exponent) for d in profile)
        return count % modulus if modulus else count
    if mode == "power":
        return tuple(sorted(
            length // gcd(length, exponent)
            for length in profile
            for _ in range(gcd(length, exponent))
        ))
    coeff = [1]
    for length in profile:
        old = coeff
        coeff = old + [0] * length
        for i, value in enumerate(old):
            coeff[i + length] = (coeff[i + length] - value) % modulus
    return tuple(c % modulus for c in coeff)


def canonical_labels(keys):
    """Encode exactly the induced equality relation, independent of the labels."""
    seen = {}
    return tuple(seen.setdefault(key, index) for index, key in enumerate(keys))


@cache
def labels_for_probe(probe, degree):
    return canonical_labels(observe(probe, p) for p in partitions(degree, degree))


def labels_for_panel(panel, degree):
    return canonical_labels(zip(*(labels_for_probe(probe, degree) for probe in panel)))


def candidate_panels(family):
    rnd = Random(SEED + FAMILIES.index(family))
    marks = [(name, t, m) for name in ("fixed", "nullity")
             for t in range(1, 23) for m in (0, 2, 3, 4, 5, 6, 7, 8, 9, 10)]
    fixed = [probe for probe in marks if probe[0] == "fixed"]
    nullity = [probe for probe in marks if probe[0] == "nullity"]
    special = {
        "extension": [("power", t, 0) for t in range(2, 31)],
        "characteristic": [("characteristic", 0, m) for m in (2, 3, 4, 5, 6, 7, 8, 9, 10)],
    }
    for _ in range(15000):
        if family == "fixed":
            yield tuple(sorted(rnd.sample(fixed, rnd.choice((2, 2, 3, 4)))))
        elif family == "nullity":
            yield tuple(sorted(rnd.sample(nullity, rnd.choice((2, 2, 3, 4)))))
        elif family == "hybrid":
            yield tuple(sorted([rnd.choice(fixed), rnd.choice(nullity)] + rnd.sample(marks, rnd.choice((0, 1, 2)))))
        else:
            yield tuple(sorted([rnd.choice(special[family])] + rnd.sample(marks, rnd.choice((1, 1, 2)))))


def search(per_family):
    registered = set()
    findings = []
    for family in FAMILIES:
        local = {}
        for panel in candidate_panels(family):
            if len(panel) != len(set(panel)):
                continue
            for n in range(2, SCAN_LIMIT + 1):
                labels = labels_for_panel(panel, n)
                if len(set(labels)) < len(labels):
                    break
            else:
                continue
            if n < 4 or len(set(labels)) < 2:
                continue
            signature = tuple(labels_for_panel(panel, d) for d in range(2, CEILING + 1))
            if signature in registered or signature in local:
                continue
            collision = next(key for key, multiplicity in Counter(labels).items() if multiplicity > 1)
            witnesses = [p for p, key in zip(partitions(n, n), labels) if key == collision]
            lhs, rhs = witnesses[:2]
            follow_on = max(8, n + 1)
            classes = len(set(labels_for_panel(panel, follow_on)))
            score = (n, int(len(witnesses) == 2), -len(panel))
            local[signature] = (score, panel, n, lhs, rhs, follow_on, classes)
            if len(local) >= 9 * per_family:
                break
        selected = sorted(local.items(), key=lambda row: row[1], reverse=True)[:per_family]
        if len(selected) != per_family:
            raise RuntimeError(f"{family} yielded {len(selected)} eligible panels")
        for signature, (_, panel, n, lhs, rhs, follow_on, classes) in selected:
            registered.add(signature)
            findings.append((family, panel, n, lhs, rhs, follow_on, classes))
    return findings


def literal_probe(probe):
    mode, exponent, modulus = probe
    if mode == "characteristic":
        return f".characteristic {modulus}"
    if mode == "power":
        return f".power {exponent}"
    return f".{mode} {exponent} {modulus}"


def literal_list(items):
    return "[" + ", ".join(str(v) for v in items) + "]"


def generate(template, output, targets, findings):
    names = []
    rows = [template.read_text(encoding="utf-8").rstrip(), ""]
    tally = Counter()
    for family, panel, n, lhs, rhs, follow_on, classes in findings:
        tally[family] += 1
        name = f"{family}_{tally[family]:02d}"
        names.append("A." + name)
        rows.append(
            f"theorem {name} : firstCollision "
            f"{literal_list(map(literal_probe, panel))} "
            f"{n} {literal_list(lhs)} {literal_list(rhs)} {follow_on} {classes} = true := by decide +kernel"
        )
    rows.extend(("", "end A"))
    output.write_text("\n".join(rows) + "\n", encoding="utf-8", newline="\n")
    targets.write_text("\n".join(names) + "\n", encoding="utf-8", newline="\n")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parent
    parser.add_argument("--template", type=Path, default=here / "A-Template.lean")
    parser.add_argument("--output", type=Path, default=here / "A.lean")
    parser.add_argument("--targets", type=Path, default=here / "A.targets")
    parser.add_argument("--per-family", type=int, default=50)
    args = parser.parse_args()
    if args.per_family < 1:
        parser.error("--per-family must be positive")
    findings = search(args.per_family)
    generate(args.template, args.output, args.targets, findings)
    print(f"{len(findings)} distinct panels in {len(FAMILIES)} families; "
          f"first cutoff distribution: {dict(sorted(Counter(row[2] for row in findings).items()))}")
    for family in FAMILIES:
        lead = next(row for row in findings if row[0] == family)
        print(lead)


if __name__ == "__main__":
    main()
