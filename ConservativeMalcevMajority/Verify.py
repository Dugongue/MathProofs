#!/usr/bin/env python3
"""Exact finite verification for the four-element hierarchical A3 example.

Requires Python 3 only; no third-party packages, floating point, or randomness.
Run: python3 verify.py
The script writes results.json next to itself and prints the same JSON.

Symbolic polynomial representation: a dict mapping sorted tuples of variable
indices to integer coefficients.  Index 4*i+a denotes the unary weight on
coordinate i at value a.  Repeated indices represent powers.  Thus the minor
checks are identities in Z[w_0,0,...,w_2,3], not numerical samples.
"""

from collections import Counter, deque
from itertools import combinations, product
import json
from pathlib import Path


D = tuple(range(4))
COORDS = tuple(range(3))
TRIPLES = tuple(product(D, repeat=3))


def root(a):
    return a // 2


def malcev(a, b, c):
    args = (a, b, c)
    bits = tuple(map(root, args))
    if bits[0] == bits[1] == bits[2]:
        return a ^ b ^ c
    minority_bit = 1 if sum(bits) == 1 else 0
    return next(v for v in args if root(v) == minority_bit)


def majority(a, b, c):
    args = (a, b, c)
    bits = tuple(map(root, args))
    if bits[0] == bits[1] == bits[2]:
        return next(v for v in args if args.count(v) >= 2)
    majority_bit = 1 if sum(bits) >= 2 else 0
    return next(v for v in args if root(v) == majority_bit)


E = {(a, b) for a, b in product(D, repeat=2) if root(a) == root(b)}
G = {(a, b) for a, b in product(D, repeat=2)
     if (a == b and a < 2) or (a >= 2 and b >= 2)}
F = {(a, b) for a, b in product(D, repeat=2)
     if (a < 2 and b < 2) or (a == b and a >= 2)}
R = {(a, b, c) for a, b, c in TRIPLES if (a, b) in G and (b, c) in F}


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def p_add(p, q):
    ans = Counter(p)
    ans.update(q)
    return {mon: coeff for mon, coeff in ans.items() if coeff}


def p_mul(p, q):
    ans = Counter()
    for left, lc in p.items():
        for right, rc in q.items():
            ans[tuple(sorted(left + right))] += lc * rc
    return {mon: coeff for mon, coeff in ans.items() if coeff}


def p_neg(p):
    return {mon: -coeff for mon, coeff in p.items()}


def atom(coord, value):
    return {(4 * coord + value,): 1}


def tuple_monomial(t):
    return tuple(4 * i + a for i, a in enumerate(t))


def proj(t, coords):
    return tuple(t[i] for i in coords)


def closure_checks(op, relation):
    count = 0
    for a, b, c in product(sorted(relation), repeat=3):
        image = tuple(op(x, y, z) for x, y, z in zip(a, b, c))
        require(image in relation,
                "Closure failure: " + repr((op.__name__, a, b, c, image)))
        count += 1
    return count


def support_blocks(matrix):
    adjacency = {}
    for (row, col), polynomial in matrix.items():
        if polynomial:
            rv, cv = ("row", row), ("col", col)
            adjacency.setdefault(rv, set()).add(cv)
            adjacency.setdefault(cv, set()).add(rv)
    unseen = set(adjacency)
    blocks = []
    while unseen:
        first = min(unseen)
        unseen.remove(first)
        todo, vertices = deque([first]), {first}
        while todo:
            vertex = todo.popleft()
            for neighbor in adjacency[vertex]:
                if neighbor not in vertices:
                    vertices.add(neighbor)
                    unseen.discard(neighbor)
                    todo.append(neighbor)
        rows = sorted(v[1] for v in vertices if v[0] == "row")
        cols = sorted(v[1] for v in vertices if v[0] == "col")
        blocks.append((rows, cols))
    return blocks


def check_partition(labels):
    X = tuple(i for i, label in enumerate(labels) if label == "X")
    Y = tuple(i for i, label in enumerate(labels) if label == "Y")
    Z = tuple(i for i, label in enumerate(labels) if label == "Z")
    matrix = {}
    for t in sorted(R):
        key = (proj(t, X), proj(t, Y))
        matrix[key] = p_add(matrix.get(key, {}), {tuple_monomial(t): 1})
    blocks = support_blocks(matrix)
    minors = 0
    full_support_cells = 0
    for rows, cols in blocks:
        for row, col in product(rows, cols):
            require(bool(matrix.get((row, col))),
                    "Nonrectangular support in partition " + repr(labels))
            full_support_cells += 1
        for r1, r2 in combinations(rows, 2):
            for c1, c2 in combinations(cols, 2):
                determinant = p_add(
                    p_mul(matrix[(r1, c1)], matrix[(r2, c2)]),
                    p_neg(p_mul(matrix[(r1, c2)], matrix[(r2, c1)])),
                )
                require(not determinant,
                        "Nonzero symbolic minor: " + repr((labels, r1, r2, c1, c2, determinant)))
                minors += 1
    return {
        "labels": list(labels), "X": list(X), "Y": list(Y), "Z": list(Z),
        "support_blocks": [
            {"rows": [list(r) for r in rows], "columns": [list(c) for c in cols]}
            for rows, cols in blocks
        ],
        "rectangular_support_cells_checked": full_support_cells,
        "symbolic_2x2_minors_checked": minors,
        "all_minors_identically_zero": True,
    }


def main():
    identity_counts = {"malcev": 0, "majority": 0}
    for x, y in product(D, repeat=2):
        require(malcev(x, y, y) == x, "First Malcev identity")
        require(malcev(y, y, x) == x, "Second Malcev identity")
        identity_counts["malcev"] += 2
        require(majority(x, x, y) == x, "First majority identity")
        require(majority(x, y, x) == x, "Second majority identity")
        require(majority(y, x, x) == x, "Third majority identity")
        identity_counts["majority"] += 3

    conservativity_counts = {}
    unary_counts = {}
    closure_counts = {}
    for op in (malcev, majority):
        for args in TRIPLES:
            require(op(*args) in args, "Conservativity failure")
        conservativity_counts[op.__name__] = len(TRIPLES)
        unary_count = 0
        for mask in range(1 << len(D)):
            unary = {a for a in D if mask & (1 << a)}
            for args in product(sorted(unary), repeat=3):
                require(op(*args) in unary, "Unary preservation failure")
                unary_count += 1
        unary_counts[op.__name__] = unary_count
        closure_counts[op.__name__] = {
            name: closure_checks(op, rel)
            for name, rel in (("E", E), ("F", F), ("G", G), ("R", R))
        }

    require(all(root(a) == root(b) == root(c) for a, b, c in R),
            "Root equality is not implicit")
    require(len(R) == 8, "Unexpected R size")
    weights = (2, 3, 5, 7)
    marginal = [[sum(weights[y] for y in D if (x, y, z) in R)
                 for z in D] for x in D]
    expected = [[2, 2, 0, 0], [3, 3, 0, 0],
                [0, 0, 5, 7], [0, 0, 5, 7]]
    require(marginal == expected, "Weighted marginal mismatch")

    # The formula is read-once in the twelve distinct variable/value symbols.
    formula = p_add(
        p_mul(p_add(p_mul(atom(0, 0), atom(1, 0)),
                    p_mul(atom(0, 1), atom(1, 1))),
              p_add(atom(2, 0), atom(2, 1))),
        p_mul(p_add(atom(0, 2), atom(0, 3)),
              p_add(p_mul(atom(1, 2), atom(2, 2)),
                    p_mul(atom(1, 3), atom(2, 3)))),
    )
    brute = {tuple_monomial(t): 1 for t in sorted(R)}
    require(formula == brute, "Polynomial formula does not match relation")

    partitions = [check_partition(labels) for labels in product("XYZ", repeat=3)]
    results = {
        "status": "ALL EXACT CHECKS PASSED",
        "domain": list(D),
        "relations": {name: [list(t) for t in sorted(rel)]
                      for name, rel in (("E", E), ("F", F), ("G", G), ("R", R))},
        "operations": {
            op.__name__: [[[op(a, b, c) for c in D] for b in D] for a in D]
            for op in (malcev, majority)
        },
        "operation_table_axis_order": "[first_argument][second_argument][third_argument]",
        "identity_checks": identity_counts,
        "conservativity_checks": conservativity_counts,
        "all_unary_relations_checked": 16,
        "unary_closure_checks": unary_counts,
        "relation_triple_closure_checks": closure_counts,
        "root_equality_implicit_in_R": True,
        "summed_coordinate": 1,
        "summed_coordinate_weights": list(weights),
        "weighted_x_z_marginal": marginal,
        "expected_x_z_marginal_matched": True,
        "polynomial_formula": "(x00*x10+x01*x11)*(x20+x21)+(x02+x03)*(x12*x22+x13*x23)",
        "polynomial_monomials_checked": len(brute),
        "polynomial_formula_equality": True,
        "coordinate_partitions_checked": len(partitions),
        "partitions_with_both_boundary_sides_nonempty": sum(bool(p["X"]) and bool(p["Y"]) for p in partitions),
        "symbolic_2x2_minors_checked_total": sum(p["symbolic_2x2_minors_checked"] for p in partitions),
        "symbolic_weights": [f"w_{i}_{a}" for i in COORDS for a in D],
        "partitions": partitions,
    }
    target = Path(__file__).resolve().with_name("results.json")
    serialized = json.dumps(results, indent=2, sort_keys=True) + "\n"
    target.write_text(serialized, encoding="utf-8")
    print(serialized, end="")


if __name__ == "__main__":
    main()
