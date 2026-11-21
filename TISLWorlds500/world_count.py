"""Evaluate the explicit Horn rules of the atlas. No completeness for mathematics is assumed."""

import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DATA = json.loads((ROOT / "world_rules.json").read_text(encoding="utf-8-sig"))
AXES = DATA["axes"]
IDS = {name: i + 1 for i, name in enumerate(AXES)}
NAMES = {i: name for name, i in IDS.items()}


def encode(name):
    if name[0] in "-!":
        return -IDS[name[1:]]
    return IDS[name.lstrip("+")]


def label(literal):
    return ("+" if literal > 0 else "-") + NAMES[abs(literal)]


def rewrite(clauses, lit):
    """Condition a CNF on one literal."""
    return tuple(sorted({tuple(x for x in clause if x != -lit)
                         for clause in clauses if lit not in clause}))


def clauses_for(excluded=()):
    blacklist = set(excluded)
    return tuple(sorted({
        tuple(sorted([-encode(name) for name in rule["when"]] + [encode(head)]))
        for rule in DATA["rules"] for head in rule["then"]
        if not (set(rule["when"]) | {head.lstrip("!")}) & blacklist
    }))


@lru_cache(None)
def restricted_count(clauses):
    """Count on exactly the variables still occurring in clauses."""
    if not clauses:
        return 1
    if () in clauses:
        return 0
    current = {abs(x) for clause in clauses for x in clause}
    unit = next((clause[0] for clause in clauses if len(clause) == 1), None)
    if unit is not None:
        variable = abs(unit)
        signs = (unit,)
    else:
        variable = Counter(abs(x) for clause in clauses for x in clause).most_common(1)[0][0]
        signs = (variable, -variable)
    result = 0
    for lit in signs:
        rest = rewrite(clauses, lit)
        remaining = {abs(x) for clause in rest for x in clause}
        result += (1 << (len(current) - len(remaining) - 1)) * restricted_count(rest)
    return result


def count(assumptions=(), excluded=()):
    if any(-x in assumptions for x in assumptions):
        return 0
    clauses = clauses_for(excluded)
    covered = set(range(1, len(IDS)+1)) - {IDS[name] for name in excluded}
    for lit in assumptions:
        assert abs(lit) in covered
        clauses = rewrite(clauses, lit)
        covered.remove(abs(lit))
    active = {abs(x) for clause in clauses for x in clause}
    return (1 << (len(covered) - len(active))) * restricted_count(clauses)


def propagate(assumptions):
    seen = {lit: "assumption" for lit in assumptions}
    for lit in tuple(seen):
        if -lit in seen:
            return seen, (lit, -lit)
    changed = True
    while changed:
        changed = False
        for rule in DATA["rules"]:
            if not all(encode(key) in seen for key in rule["when"]):
                continue
            for head in rule["then"]:
                lit = encode(head)
                if lit in seen:
                    continue
                seen[lit] = rule["id"]
                if -lit in seen:
                    return seen, (lit, -lit)
                changed = True
    return seen, ()


def certificates(trace, conflict):
    rule_map = {r["id"]: r for r in DATA["rules"]}
    wanted = set()

    def follow(lit):
        reason = trace[lit]
        if reason == "assumption" or reason in wanted:
            return
        wanted.add(reason)
        for key in rule_map[reason]["when"]:
            follow(encode(key))

    for lit in conflict:
        follow(lit)
    return [r["id"] for r in DATA["rules"] if r["id"] in wanted]


def minimal_positive_conflicts(branch, limit):
    """Inclusion-minimal positive premises of size at most limit."""
    candidates = [i for i in NAMES if i != IDS["H"]]
    found = []
    for size in range(1, limit + 1):
        for values in combinations(candidates, size):
            key = frozenset(values)
            if any(old_key <= key for old_key, _ in found):
                continue
            trace, conflict = propagate([branch, *values])
            if conflict:
                found.append((key, certificates(trace, conflict)))
    return [{"premises": [NAMES[i] for i in sorted(key)], "rules": rules}
            for key, rules in found]


def verify():
    # Independent brute force on a smaller real projection.
    selected = set(("H", "HR", "HN", "HC", "AP", "BP", "AQP", "AAP", "PZPP",
                    "PRP", "PBPP", "GRH", "RH", "HASSEQ"))
    omitted = set(AXES) - selected
    clauses = clauses_for(omitted)
    brute = 0
    for bits in product((-1, 1), repeat=len(selected)):
        literals = {IDS[k] * sign for k, sign in zip(sorted(selected), bits)}
        brute += all(set(clause) & literals for clause in clauses)
    assert brute == count(excluded=omitted)
    h = IDS["H"]
    assert count() == count((h,)) + count((-h,))
    factors = count((-h,), excluded=DATA["arithmetic_axes"])
    assert count((-h,)) == factors * 48
    for current in IDS.values():
        if current == h:
            continue
        for lit in (current, -current):
            _, conflict = propagate((-h, lit))
            assert bool(conflict) == (count((-h, lit)) == 0)
    return brute


def report():
    h = IDS["H"]
    return {
        "axes": len(AXES),
        "rules": len(DATA["rules"]),
        "raw_assignments": 1 << len(AXES),
        "retained_when_H_is_false": count((-h,)),
        "retained_when_H_is_true": count((h,)),
        "retained_when_H_is_false_and_classical_ETH_is_false": count((-h, -IDS["ETH"])),
        "retained_when_H_is_false_and_classical_ETH_is_true": count((-h, IDS["ETH"])),
        "retained_when_H_is_false_and_WEAKETH_is_true": count((-h, IDS["WEAKETH"])),
        "retained_when_H_is_false_omitting_arithmetic_axes":
            count((-h,), excluded=DATA["arithmetic_axes"]),
        "individual_branches": {
            name: {"true": count((-h, i)), "false": count((-h, -i))}
            for name, i in IDS.items() if i != h
        },
        "individual_branches_if_H": {
            name: {"true": count((h, i)), "false": count((h, -i))}
            for name, i in IDS.items() if i != h
        },
        "minimal_positive_conflicts_at_most_three": minimal_positive_conflicts(-h, 3),
        "independent_brute_force_projection": verify(),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("premises", nargs="*", help="Use +ID or !ID for a premise")
    parser.add_argument("--equality", action="store_true", help="Assume H instead of strict TI")
    parser.add_argument("--report", action="store_true", help="Report every individual branch and minimal short conflicts")
    args = parser.parse_args()
    if args.report:
        print(json.dumps(report(), indent=2))
    else:
        branch = IDS["H"] if args.equality else -IDS["H"]
        pinned = [branch, *(encode(key) for key in args.premises)]
        trace, conflict = propagate(pinned)
        print(json.dumps({"retained_assignments": count(tuple(set(pinned))),
                          "forced": {label(k): v for k, v in trace.items()},
                          "conflict": [label(k) for k in conflict],
                          "conflict_rules": certificates(trace, conflict)}, indent=2))


if __name__ == "__main__":
    main()
