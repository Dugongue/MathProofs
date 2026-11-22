"""Finite controls for the square-zero determinant-correction construction."""

from itertools import combinations, permutations
from math import gcd


def graph_pairs(limit):
    graphs = []
    for n in range(limit + 1):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = frozenset(e for i, e in enumerate(possible) if mask >> i & 1)
            graphs.append((n, edges))
    return ((a, b) for a in graphs for b in graphs)


def graph_isomorphic(a, b):
    n, edges = a
    m, other = b
    if n != m or len(edges) != len(other):
        return False
    return any(
        {tuple(sorted((perm[i], perm[j]))) for i, j in edges} == other
        for perm in permutations(range(n))
    )


def decorated(a, b, s):
    width, arrows = {}, {}
    roots = []
    common = ("common",)
    width[common] = 3 * s
    for side, (n, edges) in enumerate((a, b)):
        root = (side, "root")
        roots.append(root)
        width[root] = 1
        arrows[root, common] = s
        for vertex in range(n):
            first = (side, "first", vertex)
            second = (side, "second", vertex)
            link = (side, "link", vertex)
            width[first], width[second], width[link] = 3, 5, s
            for source in (root, first, second):
                arrows[source, link] = s
        for edge in edges:
            sink = (side, "edge", edge)
            width[sink] = 2 * s
            for vertex in edge:
                arrows[(side, "first", vertex), sink] = s
    return width, arrows, tuple(roots)


def automorphisms(width, arrows):
    # Enumerate permutations of the decorated vertices, without assuming
    # that the original vertex and edge maps control those permutations.
    def signature(x):
        return (width[x],
                sorted((width[y], arrows[x, y]) for y in width if (x, y) in arrows),
                sorted((width[y], arrows[y, x]) for y in width if (y, x) in arrows))

    signatures = {x: signature(x) for x in width}
    candidates = {x: [y for y in width if signatures[x] == signatures[y]] for x in width}
    mapping = {}
    used = set()

    def options(x):
        return [y for y in candidates[x] if y not in used
                and arrows.get((x, x)) == arrows.get((y, y))
                and all(arrows.get((x, v)) == arrows.get((y, w))
                        and arrows.get((v, x)) == arrows.get((w, y))
                        for v, w in mapping.items())]

    def descend():
        if len(mapping) == len(width):
            yield dict(mapping)
            return
        remaining = [(x, options(x)) for x in width if x not in mapping]
        x, targets = min(remaining, key=lambda entry: len(entry[1]))
        for y in targets:
            mapping[x] = y
            used.add(y)
            yield from descend()
            used.remove(y)
            del mapping[x]

    yield from descend()


def full_permutation_sign(width, arrows, mapping):
    # Explicitly permute all matrix and bimodule basis coordinates.
    diagonal = {(x,): width[x] ** 2 for x in width}
    radical = {(x, y): width[x] * width[y] * m for (x, y), m in arrows.items()}
    blocks = diagonal | radical
    offset = {}
    side = 0
    for label, length in blocks.items():
        offset[label] = side
        side += length
    images = []
    for label, length in blocks.items():
        start = offset[tuple(mapping[x] for x in label)]
        images.extend(range(start, start + length))
    seen = set()
    sign = 1
    for start in range(side):
        if start in seen:
            continue
        point = start
        length = 0
        while point not in seen:
            seen.add(point)
            length += 1
            point = images[point]
        sign *= (-1) ** (length - 1)
    return sign


def run_pair(a, b, s):
    width, arrows, roots = decorated(a, b, s)
    side = sum(n*n for n in width.values()) + sum(
        width[x] * width[y] * m for (x, y), m in arrows.items()
    )
    assert side == (2 + 15 * s*s + (34 + 10*s*s) * (a[0]+b[0])
                    + 16 * s*s * (len(a[1])+len(b[1])))
    assert all((x, x) not in arrows for x in width)
    left = {x: width[x] + sum(width[y] * arrows.get((x, y), 0) for y in width) for x in width}
    right = {x: width[x] + sum(width[y] * arrows.get((y, x), 0) for y in width) for x in width}
    assert gcd(s, *left.values()) == gcd(s, *right.values()) == 1
    assert all((left[x]-right[x]) % s == 0 for x in width)
    assert all(width[x]*width[y] % s == 0 for x, y in arrows)
    found_negative = False
    tested = 0
    for mapping in automorphisms(width, arrows):
        sign = full_permutation_sign(width, arrows, mapping)
        assert (sign == -1) == (mapping[roots[0]] == roots[1])
        found_negative |= sign == -1
        tested += 1
    assert found_negative == graph_isomorphic(a, b)
    return tested


def main():
    for s in (2, 4, 6):
        trials = tuple(graph_pairs(3))
        count = sum(run_pair(a, b, s) for a, b in trials)
        print(f"s={s}: {len(trials)} input pairs and {count} decorated automorphisms checked.")


if __name__ == "__main__":
    main()
