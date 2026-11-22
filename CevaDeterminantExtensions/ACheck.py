"""Independent finite controls for the pinned-scale and perfect-pairing counts."""

from itertools import combinations, product
from math import gcd
from time import perf_counter


def component_blocks(vertices, edges, mask):
    blocks = [{v} for v in range(vertices)]
    for i, (u, v) in enumerate(edges):
        if (mask >> i) & 1:
            left = next(block for block in blocks if u in block)
            right = next(block for block in blocks if v in block)
            if left is not right:
                left.update(right)
                blocks.remove(right)
    return sorted(tuple(sorted(block)) for block in blocks)


def all_subsets(mask):
    subset = mask
    while True:
        yield subset
        if not subset:
            break
        subset = (subset - 1) & mask


def assignment_tables(modulus, subgroup, vertices, weights):
    edges = tuple(combinations(range(vertices), 2))
    count = 1 << len(edges)
    units = [u for u in range(modulus) if gcd(u, modulus) == 1]
    inverses = {u: pow(u, -1, modulus) for u in units}
    connected = [
        mask for mask in range(count)
        if len(component_blocks(vertices, edges, mask)) == 1
    ]
    assignments = []
    for values in product(units, repeat=vertices):
        equal = 0
        allowed = 0
        for i, (u, v) in enumerate(edges):
            if values[u] == values[v]:
                equal |= 1 << i
            if values[u] * inverses[values[v]] % modulus in subgroup:
                allowed |= 1 << i
        determinant = 1
        for x, weight in zip(values, weights):
            determinant = determinant * pow(x, weight, modulus) % modulus
        assignments.append((allowed, equal, determinant))
    for graph in connected:
        counts = [0] * count
        detcounts = [0] * count
        for allowed, equal, determinant in assignments:
            if graph & allowed == graph:
                counts[equal] += 1
                if determinant == 1:
                    detcounts[equal] += 1
        for i in range(len(edges)):
            for mask in range(count):
                if not mask & (1 << i):
                    counts[mask] += counts[mask | (1 << i)]
                    detcounts[mask] += detcounts[mask | (1 << i)]
        yield edges, graph, units, counts, detcounts


def terminal_partition(order, edges, failed, counts, group_size):
    edge_index = {edge: i for i, edge in enumerate(edges)}
    found = []
    query_count = 0
    for vertex in order:
        def matches(candidates):
            nonlocal query_count
            query_count += 1
            star = sum(
                1 << edge_index[tuple(sorted((vertex, block[0])))]
                for block in candidates
            )
            return counts[failed] == (
                counts[failed | star] * group_size ** (len(candidates) - 1)
            )

        if not found or not matches(found):
            found.append([vertex])
            continue
        lo, hi = 0, len(found)
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if matches(found[lo:mid]):
                hi = mid
            else:
                lo = mid
        found[lo].append(vertex)
    return sorted(tuple(sorted(block)) for block in found), query_count


def check_graph_counts():
    cases = 0
    partitions = 0
    max_queries = 0
    for modulus, group in ((7, (1, 2, 4)), (8, (1, 3, 5, 7)), (9, (1, 4, 7))):
        for weights in ((0, 0, 0, 0), (1, 1, 0, -2), (2, -4, 5, -3)):
            for edges, graph, units, actual, actual_det in assignment_tables(
                modulus, group, 4, weights
            ):
                for failed in all_subsets(graph):
                    neutral = len(component_blocks(4, edges, failed))
                    for pins in range(1 << len(edges)):
                        merged = failed | pins
                        parts = component_blocks(4, edges, merged)
                        expected = len(units) * len(group) ** (len(parts) - 1)
                        assert actual[merged] == expected
                        assert actual[failed] == actual[merged] * len(group) ** (
                            neutral - len(parts)
                        )
                        possible = {1}
                        for block in parts:
                            mass = sum(weights[v] for v in block)
                            possible = {
                                x * pow(y, mass, modulus) % modulus
                                for x in possible for y in group
                            }
                        assert actual_det[merged] * len(possible) == actual[merged]
                        cases += 1
                    recovered, queries = terminal_partition(
                        (0, 1, 2, 3), edges, failed, actual, len(group)
                    )
                    assert recovered == component_blocks(4, edges, failed)
                    max_queries = max(max_queries, queries)
                    partitions += 1
    print(f"{cases:,} exhaustive coordinate counts and {partitions:,} terminal partitions.")
    print(f"At most {max_queries} star queries per four-vertex partition.")


def times(a, b):
    return tuple(
        sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % 3
        for i in range(2) for j in range(2)
    )


def scale(a, scalar):
    return tuple(scalar * x % 3 for x in a)


def check_matrix_pairing():
    identity = (1, 0, 0, 1)
    matrices = tuple(product(range(3), repeat=4))
    invertible = [
        matrix for matrix in matrices
        if (matrix[0] * matrix[3] - matrix[1] * matrix[2]) % 3
    ]
    inverse = {
        matrix: next(b for b in invertible if times(matrix, b) == identity)
        for matrix in invertible
    }
    actions = {
        tuple(times(times(matrix, e), inverse[matrix]) for e in matrices): matrix
        for matrix in invertible
    }
    assert 2 * len(actions) == len(invertible)
    matrix_units = (
        (1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1),
    )
    for action, matrix in actions.items():
        images = tuple(action[matrices.index(e)] for e in matrix_units)
        row = [
            r for r in invertible
            if all(times(e, r) == times(r, image)
                   for e, image in zip(matrix_units, images))
        ]
        col = [
            c for c in invertible
            if all(times(c, e) == times(image, c)
                   for e, image in zip(matrix_units, images))
        ]
        assert set(row) == {inverse[matrix], scale(inverse[matrix], 2)}
        assert set(col) == {matrix, scale(matrix, 2)}
        for multiplier in (1, 2):
            assert sum(
                times(r, c) == scale(identity, multiplier)
                for r in row for c in col
            ) == 2
    print(f"{len(actions)} matrix actions checked against both pairing multipliers over F3.")


if __name__ == "__main__":
    start = perf_counter()
    check_graph_counts()
    check_matrix_pairing()
    print(f"Controls completed in {perf_counter() - start:.2f} seconds.")
