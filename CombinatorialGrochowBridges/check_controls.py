"""Exact small controls for the four mathematical arguments. Python 3.10+."""

from collections import Counter
from itertools import combinations, permutations, product


def adjacency(order, edges):
    edge_set = {frozenset(edge) for edge in edges}
    return tuple(tuple(int(frozenset((u, v)) in edge_set)
                       for v in range(order)) for u in range(order))


def walk_count(matrix, length):
    counts = [1] * len(matrix)
    for _ in range(length):
        counts = [sum(a * b for a, b in zip(row, counts)) for row in matrix]
    return sum(counts)


def delete_vertex(matrix, vertex):
    return tuple(tuple(x for j, x in enumerate(row) if j != vertex)
                 for i, row in enumerate(matrix) if i != vertex)


def joint_two_wl(first, second):
    matrices = (first, second)
    n = len(first)

    def compress(signatures):
        palette = {value: color for color, value in
                   enumerate(sorted(set(signatures.values())))}
        return {key: palette[value] for key, value in signatures.items()}

    colors = compress({(g, u, v): (u == v, matrix[u][v])
                       for g, matrix in enumerate(matrices)
                       for u in range(n) for v in range(n)})
    while True:
        refined = compress({
            (g, u, v): (color, tuple(sorted(
                (colors[g, u, z], colors[g, z, v]) for z in range(n))))
            for (g, u, v), color in colors.items()
        })
        if len(set(refined.values())) == len(set(colors.values())):
            break
        colors = refined
    return (Counter(c for (g, _, _), c in refined.items() if g == 0) ==
            Counter(c for (g, _, _), c in refined.items() if g == 1))


def graph_control():
    cycle = adjacency(6, [(i, (i + 1) % 6) for i in range(6)])
    triangles = adjacency(6, [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)])
    cards = [Counter(walk_count(delete_vertex(matrix, v), 3)
                     for v in range(6)) for matrix in (cycle, triangles)]
    assert all(sum(row) == 2 for matrix in (cycle, triangles) for row in matrix)
    assert cards == [Counter({24: 6}), Counter({26: 6})]
    assert not joint_two_wl(cycle, triangles)

    grid = list(product(range(4), repeat=2))
    pairs = list(combinations(range(len(grid)), 2))
    rook = adjacency(16, [(u, v) for u, v in pairs
                          if any(a == b for a, b in zip(grid[u], grid[v]))])
    steps = {(0, 1), (0, 3), (1, 0), (3, 0), (1, 1), (3, 3)}
    shrikhande = adjacency(16, [
        (u, v) for u, v in pairs
        if tuple((a - b) % 4 for a, b in zip(grid[u], grid[v])) in steps
    ])
    assert joint_two_wl(rook, shrikhande)
    decks = [
        Counter(tuple(walk_count(delete_vertex(matrix, v), length)
                      for length in range(1, 7)) for v in range(16))
        for matrix in (rook, shrikhande)
    ]
    assert decks[0] == decks[1]
    print("Graph edits: C6 and two triangles split at 2-WL; "
          "rook and Shrikhande agree on six joint path coordinates.")


def cover_control():
    # Patches {0,1} and {2,3}, anchors 0 and 2.
    inside = ((0, 1, 1), (2, 3, 1))
    outside = ((1, 3, 1), (1, 2, 3), (3, 0, 3))

    for q, expected in ((2, 4), (3, 5)):
        labels = range(q)
        deficit = 0
        transformed_cut_min = sum(w for _, _, w in outside)
        worst_loss = 0
        worst_gap = 0
        for x1, x3 in product(range(2), repeat=2):
            x = (0, x1, 0, x3)
            internal_cost = sum(w for u, v, w in inside if x[u] != x[v])
            exposure = sum(w for u, v, w in outside
                           if (x[u] != x[v] if q == 2 else x[u] or x[v]))
            deficit = max(deficit, exposure - internal_cost)
            y1, y3 = x1, 1 - x3
            cross_term = int(y1 != y3) if q == 2 else (1 - y1) * y3
            transformed_cut_min = min(
                transformed_cut_min, y1 + (1 - y3) + cross_term
                + 3 * (1 - y1) + 3 * y3)
        for constraints in product(tuple(permutations(labels)), repeat=3):
            def score(values):
                return (sum(w for u, v, w in inside if values[u] == values[v])
                        + sum(w for (u, v, w), p in zip(outside, constraints)
                              if p[values[u]] == values[v]))

            global_optimum = 0
            quotient_optimum = 0
            for values in product(labels, repeat=4):
                a, _, b, _ = values
                rounded = (a, a, b, b)
                original_score = score(values)
                rounded_score = score(rounded)
                worst_loss = max(worst_loss, original_score - rounded_score)
                global_optimum = max(global_optimum, original_score)
                quotient_optimum = max(quotient_optimum, rounded_score)
            worst_gap = max(worst_gap, global_optimum - quotient_optimum)
        assert deficit == worst_loss == expected
        assert transformed_cut_min == 7 - deficit
        assert worst_gap == 2
        print(f"Cover contraction (q={q}): sharp rounding loss {deficit}, "
              f"largest optimized gap {worst_gap}.")


def optimization_control():
    # Verify the sample identity at grid points including the affine boundary.
    # Double all values to check a half-integral grid using integers.
    boundary = 0
    for w1, w2 in product(range(21), repeat=2):
        if w1 - w2 >= 2:
            output = max(w1 + w2, 2 * w2 + 2)
        else:
            output = max(w1 + w2, 2 * w1 - 2)
        assert output == w1 + w2
        boundary += w1 - w2 == 2
    assert boundary == 19

    exponents = ((3, 0), (2, 1), (1, 1), (0, 2))
    for w1, w2 in product(range(-10, 11), repeat=2):
        nested = max(2 * w1, w2) + max(w1, w2)
        assert nested == max(a * w1 + b * w2 for a, b in exponents)

    # The two slope polytopes are segments. Check their coordinate supports:
    # h_Q_yes(1,0)=1, h_Q_no(0,1)=1. Both contain (1,1).
    yes, no = ((1, 1), (0, 2)), ((1, 1), (2, 0))
    assert max(x for x, _ in yes) == max(y for _, y in no) == 1
    assert max(y for _, y in yes) == max(x for x, _ in no) == 2
    assert (1, 1) in set(yes) & set(no)
    print("Optimization: 441 objective checks for each of the guarded box "
          "and the nested permanent oracle.")


def tensor_control():
    # GL(2,2) matrices in row-major order. Over F_2, PGL = GL.
    gl = [m for m in product(range(2), repeat=4)
          if (m[0] * m[3] - m[1] * m[2]) % 2]
    identity = (1, 0, 0, 1)
    shear = (1, 1, 0, 1)
    rotate = (0, 1, 1, 1)

    def mul(a, b):
        return tuple(sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % 2
                     for i, j in product(range(2), repeat=2))

    inverse = {a: next(b for b in gl if mul(a, b) == identity) for a in gl}
    tree = [(0, 2), (0, 3), (1, 3)]
    cycle = tree + [(1, 2)]
    target = [shear, rotate, shear]

    def has_switch(edges, gains):
        return any(
            all(mul(switches[u], inverse[switches[v]]) == gain
                for (u, v), gain in zip(edges, gains))
            for switches in product(gl, repeat=4)
        )

    assert has_switch(tree, target)
    possible_close = [edge for edge in gl if has_switch(cycle, target + [edge])]
    assert possible_close == [mul(mul(shear, inverse[rotate]), shear)]
    print("Tensor gain graphs: all tree constraints switch; exactly one closing "
          "gain works on the four-cycle.")


if __name__ == "__main__":
    graph_control()
    tensor_control()
    optimization_control()
    cover_control()
