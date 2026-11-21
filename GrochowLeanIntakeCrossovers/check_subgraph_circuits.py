"""Compare the cut-contraction recurrence with direct weighted injection sums."""

from itertools import combinations, permutations, product
from math import prod
from random import Random


def make_instance(tree, rank, modulus, rng):
    transfer, bridge, leaf, dense = {}, {}, {}, {}

    def matrix():
        return tuple(tuple(rng.randrange(modulus) for _ in range(rank)) for _ in range(rank))

    def visit(node):
        if isinstance(node, int):
            leaf[node] = tuple(rng.randrange(modulus) for _ in range(rank))
            return {node: leaf[node]}
        a, b = node
        left, right = visit(a), visit(b)
        c = bridge[node] = matrix()
        for u, lrow in left.items():
            for v, rrow in right.items():
                w = sum(lrow[i] * c[i][j] * rrow[j] for i in range(rank) for j in range(rank))
                dense[u, v] = dense[v, u] = w % modulus
        answer = {}
        for child, rows in ((a, left), (b, right)):
            m = transfer[child] = matrix()
            for u, row in rows.items():
                answer[u] = tuple(sum(row[i] * m[i][j] for i in range(rank)) % modulus
                                  for j in range(rank))
        return answer

    visit(tree)
    return leaf, transfer, bridge, dense


def contraction(tree, k, edges, weights, rank, modulus, data, induced):
    leaf, transfer, bridge, _ = data
    base_rank = rank
    interactions = tuple(combinations(range(k), 2)) if induced else tuple(sorted(edges))
    if induced:
        rank += 1

    def pad(matrix, sign, corner):
        if not induced:
            return matrix
        return tuple(tuple(sign * v for v in row) + (0,) for row in matrix) + (
            (0,) * base_rank + (corner,),
        )

    subsets = [frozenset(i for i in range(k) if mask & (1 << i)) for mask in range(1 << k)]
    boundaries = {p: [e for e in interactions if (e[0] in p) != (e[1] in p)] for p in subsets}
    labels = [tuple(product(range(rank), repeat=j)) for j in range(len(interactions) + 1)]

    def change_mode(table, mode, matrix):
        return {
            key: sum(table[key[:mode] + (i,) + key[mode + 1:]] * matrix[i][key[mode]]
                     for i in range(rank)) % modulus
            for key in table
        }

    def visit(node):
        if isinstance(node, int):
            row = leaf[node] + ((1,) if induced else ())
            return {
                p: {idx: (weights[next(iter(p)), node] * prod(row[i] for i in idx)) % modulus
                    if len(p) == 1 else int(not p)
                    for idx in labels[len(boundaries[p])]}
                for p in subsets
            }
        a, b = node
        left, right = visit(a), visit(b)
        answer = {}
        for p in subsets:
            outside = boundaries[p]
            result = dict.fromkeys(labels[len(outside)], 0)
            for pa in subsets:
                if not pa <= p:
                    continue
                pb = p - pa
                la, lb = boundaries[pa], boundaries[pb]
                crossing = [e for e in la if e in lb]
                a_table, b_table = left[pa], right[pb]
                for mode, edge in enumerate(la):
                    if edge in crossing:
                        sign, corner = (1, 0) if edge in edges else (-1, 1)
                        matrix = pad(bridge[node], sign, corner)
                    else:
                        matrix = pad(transfer[a], 1, 1)
                    a_table = change_mode(a_table, mode, matrix)
                for mode, edge in enumerate(lb):
                    if edge not in crossing:
                        b_table = change_mode(b_table, mode, pad(transfer[b], 1, 1))
                for lab in result:
                    assignment = dict(zip(outside, lab))
                    for inner in labels[len(crossing)]:
                        assignment.update(zip(crossing, inner))
                        result[lab] += (a_table[tuple(assignment[e] for e in la)]
                                        * b_table[tuple(assignment[e] for e in lb)])
                    result[lab] %= modulus
            answer[p] = result
        return answer

    return visit(tree)[subsets[-1]][()]


def direct(vertices, k, edges, weights, dense, modulus, induced):
    total = 0
    for image in permutations(vertices, k):
        term = prod(weights[i, v] for i, v in enumerate(image))
        for i, j in combinations(range(k), 2):
            if (i, j) in edges:
                term *= dense[image[i], image[j]]
            elif induced:
                term *= 1 - dense[image[i], image[j]]
        total += term
    return total % modulus


def main():
    rng = Random(20261121)
    tree = (0, ((1, 2), (3, 4)))
    checks = 0
    for modulus in (2, 7, 101):
        for rank in (1, 2):
            data = make_instance(tree, rank, modulus, rng)
            patterns = [(0, set()), (1, set()), (2, {(0, 1)}), (4, {(0, 1), (2, 3)})]
            pairs = tuple(combinations(range(3), 2))
            patterns += [(3, {e for i, e in enumerate(pairs) if mask & (1 << i)})
                         for mask in range(1 << len(pairs))]
            for k, edges in patterns:
                weights = {(i, j): rng.randrange(modulus) for i in range(k) for j in data[0]}
                for induced in (False, True):
                    actual = contraction(tree, k, edges, weights, rank, modulus, data, induced)
                    expected = direct(data[0], k, edges, weights, data[3], modulus, induced)
                    assert actual == expected, (modulus, rank, k, edges, induced, actual, expected)
                    checks += 1
    print(f"{checks} weighted contraction checks passed")


if __name__ == "__main__":
    main()
