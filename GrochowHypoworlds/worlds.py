"""Replay the finite propositional consequences of the Grochow question ledger."""

import argparse
import csv
import itertools
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent
PROFILES = {"published": {"published"}, "local": {"published", "local"}}


def table(name, columns):
    for number, line in enumerate((ROOT / name).read_text(encoding="utf-8").splitlines(), 1):
        if not line.strip() or line.startswith("#"):
            continue
        fields = [field.strip() for field in line.split("|", columns - 1)]
        if len(fields) != columns or not all(fields):
            raise ValueError(f"{name}, line {number}: expected {columns} nonempty fields")
        yield fields


def find_model(clauses, assumptions=()):
    """Complete Davis–Putnam–Logemann–Loveland search on signed integers."""
    if any(-literal in assumptions for literal in assumptions):
        return None

    def search(pending, assigned, new):
        while new:
            assigned.update(new)
            reduced = []
            next_units = set()
            for clause in pending:
                if any(literal in new for literal in clause):
                    continue
                remaining = tuple(literal for literal in clause if -literal not in new)
                if not remaining:
                    return None
                if len(remaining) == 1:
                    next_units.add(remaining[0])
                reduced.append(remaining)
            pending = reduced
            if any(-literal in assigned or -literal in next_units for literal in next_units):
                return None
            new = next_units - assigned
        if not pending:
            return assigned
        if all(any(literal < 0 for literal in clause) for clause in pending):
            return assigned
        choice = min(pending, key=len)[0]
        branch = search(pending, assigned.copy(), {choice})
        if branch is not None:
            return branch
        return search(pending, assigned, {-choice})

    if any(not clause for clause in clauses):
        return None
    units = {clause[0] for clause in clauses if len(clause) == 1}
    units.update(assumptions)
    if any(-literal in units for literal in units):
        return None
    return search(clauses, set(), units)


def load(profile):
    atoms = {}
    for name, row, statement in table("claims.txt", 3):
        if name in atoms:
            raise ValueError(f"duplicate claim {name}")
        atoms[name] = {"row": row, "statement": statement}
    index = {name: number for number, name in enumerate(atoms, 1)}

    def encode(text):
        return -index[text[1:]] if text.startswith("!") else index[text]

    rules = []
    seen = set()
    for name, source_class, formula, proof, reference in table("rules.txt", 5):
        if name in seen or source_class not in PROFILES["local"]:
            raise ValueError(f"invalid or duplicate rule {name}")
        seen.add(name)
        if "->" in formula:
            left, right = formula.split("->", 1)
            clause = tuple(-encode(part.strip()) for part in left.split("&"))
            if right.strip() != "False":
                clause += tuple(encode(part.strip()) for part in right.split(","))
        else:
            clause = tuple(encode(part.strip()) for part in formula.split(","))
        if source_class in PROFILES[profile]:
            rules.append((tuple(dict.fromkeys(clause)), {
                "id": name, "status": source_class, "formula": formula,
                "reason": proof, "source": reference,
            }))
    return atoms, index, encode, rules


def scan(atoms, index, clauses, profile, output):
    if find_model(clauses) is None:
        raise ValueError("base ledger is inconsistent")
    if output:
        output.mkdir(parents=True, exist_ok=True)

    neighbors = {number: set() for number in index.values()}
    for clause in clauses:
        variables = {abs(literal) for literal in clause}
        anchor = min(variables)
        for variable in variables:
            neighbors[anchor].add(variable)
            neighbors[variable].add(anchor)
    components = {}
    for number in index.values():
        frontier = [number]
        while frontier:
            variable = frontier.pop()
            if variable not in components:
                components[variable] = number
                frontier.extend(neighbors[variable])
    by_component = {component: [] for component in components.values()}
    for clause in clauses:
        by_component[components[abs(clause[0])]].append(clause)

    signs = {}
    for name, number in index.items():
        relevant = by_component[components[number]]
        signs[name] = {sign for sign in (1, -1) if find_model(relevant, (sign * number,)) is not None}

    excluded = []
    equivalent = []
    opposite = []
    surviving_pairs = 0
    pairs_checked = 0
    all_pairs = []
    for left, right in itertools.combinations(index, 2):
        left_id, right_id = index[left], index[right]
        same_component = components[left_id] == components[right_id]
        relevant = by_component[components[left_id]]
        pattern = set()
        for first, second in itertools.product((1, -1), repeat=2):
            pairs_checked += 1
            possible = first in signs[left] and second in signs[right]
            if possible and (not same_component
                             or find_model(relevant, (first * left_id, second * right_id)) is not None):
                surviving_pairs += 1
                pattern.add((first, second))
                state = "satisfiable"
            elif possible:
                excluded.append([left if first > 0 else "!" + left, right if second > 0 else "!" + right])
                state = "contradiction"
            else:
                state = "excluded by single claim"
            all_pairs.append((left, first, right, second, state))
        if signs[left] == signs[right] == {1, -1}:
            if pattern == {(1, 1), (-1, -1)}:
                equivalent.append([left, right])
            if pattern == {(1, -1), (-1, 1)}:
                opposite.append([left, right])

    summary = {
        "profile": profile,
        "catalog_rows": sorted({entry["row"] for entry in atoms.values()} - {"background"}),
        "atoms": len(atoms),
        "clauses": len(clauses),
        "forced_true": [key for key, values in signs.items() if values == {1}],
        "forced_false": [key for key, values in signs.items() if values == {-1}],
        "both_signs_satisfiable": [key for key, values in signs.items() if values == {1, -1}],
        "pair_assignments_checked": pairs_checked,
        "satisfiable_pair_assignments": surviving_pairs,
        "pair_only_contradictions": excluded,
        "nonconstant_equivalences": equivalent,
        "nonconstant_oppositions": opposite,
    }
    if output:
        (output / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        with (output / "pairs.csv").open("w", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(("claim_a", "sign_a", "claim_b", "sign_b", "status"))
            writer.writerows(all_pairs)
        with (output / "implications.csv").open("w", encoding="utf-8", newline="") as handle:
            writer = csv.writer(handle)
            writer.writerow(("assume", "follows"))
            for left, right in excluded:
                negate = lambda name: name[1:] if name.startswith("!") else "!" + name
                writer.writerow((left, negate(right)))
                writer.writerow((right, negate(left)))
    return summary


def explain(rules, assumptions):
    model = find_model([clause for clause, _ in rules], assumptions)
    if model is not None:
        return model, []
    core = list(rules)
    for rule in rules:
        candidate = [item for item in core if item is not rule]
        if find_model([clause for clause, _ in candidate], assumptions) is None:
            core = candidate
    return None, [evidence for _, evidence in core]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", default="local", choices=PROFILES)
    parser.add_argument("--output", type=Path, help="write the full scan to a directory")
    parser.add_argument("--assume", nargs="+", help="signed claims, for example G01 !G02")
    args = parser.parse_args()
    atoms, index, encode, rules = load(args.profile)
    if args.assume:
        model, core = explain(rules, tuple(map(encode, args.assume)))
        if model is None:
            result = {"status": "contradiction", "assumptions": args.assume, "rule_core": core}
        else:
            result = {"status": "satisfiable in ledger", "assumptions": args.assume,
                      "one_model": {name: number in model for name, number in index.items()}}
    else:
        result = scan(atoms, index, [clause for clause, _ in rules], args.profile, args.output)
    print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
