"""Check class-constant inverse diagonals for connected and disconnected supports."""

from check_quiver_degree import rref


def reverse_constants(source, target, forward, p):
    edges = [(j, i) for j, row in enumerate(forward) for i, entry in enumerate(row) if entry % p]
    equations = [
        [int(k == j) for k, _ in edges] + [count]
        for j, count in enumerate(target)
    ] + [
        [int(k == i) for _, k in edges] + [count]
        for i, count in enumerate(source)
    ]
    reduced, pivots = rref(equations, len(edges) + 1, p)
    if len(edges) in pivots:
        return None
    reverse = [[0] * len(target) for _ in source]
    for row, pivot in zip(reduced, pivots):
        j, i = edges[pivot]
        denominator = target[j] * source[i] * forward[j][i] % p
        reverse[i][j] = row[-1] * pow(denominator, -1, p) % p
    assert all(
        sum(c * forward[j][i] * reverse[i][j] for i, c in enumerate(source)) % p == 1
        for j in range(len(target))
    )
    assert all(
        sum(c * reverse[i][j] * forward[j][i] for j, c in enumerate(target)) % p == 1
        for i in range(len(source))
    )
    return reverse


def class_sizes(total, p):
    for x in range(total // (p + 1) + 1):
        rest = total - x * (p + 1)
        if rest % (2 * p + 1) == 0:
            return [p + 1] * x + [2 * p + 1] * (rest // (2 * p + 1))
    raise ValueError("class total too small")


def weights(counts, p):
    return [
        (key, count)
        for key, total in enumerate(counts)
        for count in class_sizes(total, p)
    ]


def class_matrix(source, target, allowed):
    return [[int((a, b) in allowed) for a, _ in source] for b, _ in target]


def forward_one_arrow_equations(p, gap):
    base = (p + 1) * (2 * p + 1)
    source = weights([base, base + gap], p)
    target = weights([base + gap, base], p)
    input_maps = class_matrix(source, target, {(0, 0), (0, 1), (1, 1)})
    output_maps = class_matrix(source, target, {(0, 0), (1, 0), (1, 1)})
    for j, (t, _) in enumerate(target):
        for i, (s, _) in enumerate(source):
            assert output_maps[j][i] * (s == 0) == (t == 0) * input_maps[j][i]
    source_counts = [c for _, c in source]
    target_counts = [c for _, c in target]
    assert reverse_constants(source_counts, target_counts, input_maps, p) is not None
    assert reverse_constants(source_counts, target_counts, output_maps, p) is not None


def disconnected_components(p, gap):
    base = (p + 1) * (2 * p + 1)
    source = weights([base + gap, base], p)
    target = weights([base, base + gap], p)
    forward = class_matrix(source, target, {(0, 0), (1, 1)})
    answer = reverse_constants([c for _, c in source], [c for _, c in target], forward, p)
    assert (answer is not None) == (gap % p == 0)


if __name__ == "__main__":
    for p in (2, 3, 5, 7):
        for gap in (1, p, p + 1):
            forward_one_arrow_equations(p, gap)
            disconnected_components(p, gap)
    print("Verified 24 weighted inverse-diagonal systems and 12 class-constant forward-arrow assignments.")
