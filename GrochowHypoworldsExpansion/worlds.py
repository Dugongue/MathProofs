"""Replay the finite propositional consequences of the Grochow question ledger."""

import argparse
import csv
import itertools
import json
from functools import lru_cache
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


def split_components(clauses, variables):
    neighbors = {number: set() for number in variables}
    for clause in clauses:
        support = {abs(literal) for literal in clause}
        anchor = min(support)
        for variable in support:
            neighbors[anchor].add(variable)
            neighbors[variable].add(anchor)
    components = {}
    for number in variables:
        frontier = [number]
        while frontier:
            variable = frontier.pop()
            if variable not in components:
                components[variable] = number
                frontier.extend(neighbors[variable])
    by_component = {component: [] for component in components.values()}
    for clause in clauses:
        by_component[components[abs(clause[0])]].append(clause)
    return components, by_component


def count_models(clauses, variables):
    """Count all complete assignments, including unused variables."""
    def canonical(conditions):
        unique = {tuple(sorted(set(clause))) for clause in conditions
                  if not any(-lit in clause for lit in clause)}
        return tuple(sorted(unique))

    def support(conditions):
        return {abs(lit) for clause in conditions for lit in clause}

    @lru_cache(maxsize=None)
    def count_active(conditions):
        if not conditions:
            return 1
        if () in conditions:
            return 0
        active = support(conditions)
        _, parts = split_components(conditions, sorted(active))
        if len(parts) > 1:
            result = 1
            for part in parts.values():
                result *= count_active(canonical(part))
            return result
        choice = min(conditions, key=len)[0]
        options = (choice,) if (choice,) in conditions else (choice, -choice)
        total = 0
        for selected in options:
            reduced = canonical(tuple(lit for lit in clause if lit != -selected)
                                for clause in conditions if selected not in clause)
            free = len(active) - 1 - len(support(reduced))
            total += (1 << free) * count_active(reduced)
        return total

    normal = canonical(clauses)
    return (1 << (len(set(variables)) - len(support(normal)))) * count_active(normal)


def scan(atoms, index, clauses, profile, output, triples=False):
    if find_model(clauses) is None:
        raise ValueError("base ledger is inconsistent")
    if output:
        output.mkdir(parents=True, exist_ok=True)

    components, by_component = split_components(clauses, list(index.values()))

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
    pair_models = {}
    for left, right in itertools.combinations(index, 2):
        left_id, right_id = index[left], index[right]
        same_component = components[left_id] == components[right_id]
        relevant = by_component[components[left_id]]
        pattern = set()
        for first, second in itertools.product((1, -1), repeat=2):
            pairs_checked += 1
            possible = first in signs[left] and second in signs[right]
            pair = (first * left_id, second * right_id)
            model = find_model(relevant, pair) if possible and same_component else None
            if possible and (not same_component or model is not None):
                surviving_pairs += 1
                pattern.add((first, second))
                state = "satisfiable"
                if triples and same_component:
                    pair_models[pair] = model
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
        "complete_assignments_satisfying_ledger": str(count_models(clauses, index.values())),
    }
    triple_conflicts = []
    if triples:
        compared = 0
        variable_names = {number: name for name, number in index.items()}
        # A minimal conflict cannot straddle independent clause components.
        for part, relevant in by_component.items():
            candidates = [(name, number) for name, number in index.items()
                          if components[number] == part and len(signs[name]) == 2]
            for (_, a), (_, b), (_, c) in itertools.combinations(candidates, 3):
                for sa, sb, sc in itertools.product((1, -1), repeat=3):
                    x, y, z = sa * a, sb * b, sc * c
                    first = pair_models.get((x, y))
                    second = pair_models.get((x, z))
                    third = pair_models.get((y, z))
                    if first is None or second is None or third is None:
                        continue
                    compared += 1

                    def holds(literal, witness):
                        return literal in witness if literal > 0 else -literal not in witness

                    if holds(z, first) or holds(y, second) or holds(x, third):
                        continue
                    if find_model(relevant, (x, y, z)) is None:
                        triple_conflicts.append([
                            ("" if lit > 0 else "!") + variable_names[abs(lit)]
                            for lit in (x, y, z)
                        ])
        summary["triple_candidates_with_viable_pairs"] = compared
        summary["minimal_triple_contradictions"] = len(triple_conflicts)
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
        if triples:
            with (output / "minimal-triples.csv").open("w", encoding="utf-8", newline="") as handle:
                writer = csv.writer(handle)
                writer.writerow(("first_literal", "second_literal", "third_literal"))
                writer.writerows(triple_conflicts)
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
    parser.add_argument("--triples", action="store_true", help="find all minimal three-literal contradictions")
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
        result = scan(atoms, index, [clause for clause, _ in rules], args.profile, args.output, args.triples)
    print(json.dumps(result, indent=2, ensure_ascii=True))


if __name__ == "__main__":
    main()
