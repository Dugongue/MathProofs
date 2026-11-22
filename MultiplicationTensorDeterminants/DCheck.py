"""Direct finite checks for the graph encoding, path signs and chain bound."""
from collections import Counter, defaultdict
from itertools import combinations, permutations, product


def sign(permutation):
    seen = set()
    cycles = 0
    for i in range(len(permutation)):
        if i in seen:
            continue
        cycles += 1
        while i not in seen:
            seen.add(i)
            i = permutation[i]
    return (-1) ** (len(permutation) - cycles)


def graph_edges(n):
    pairs = tuple(combinations(range(n), 2))
    for bits in product((False, True), repeat=len(pairs)):
        yield frozenset(edge for edge, bit in zip(pairs, bits) if bit)


def moved(edges, order):
    return frozenset(tuple(sorted((order[i], order[j]))) for i, j in edges)


def make_quiver(n, edges):
    middles = {}
    for j in range(n):
        middles[0, n + 1 + j] = tuple(range(3))
        middles[1 + j, n + 1 + j] = tuple(range(2))
    for i, j in edges:
        middles[1 + i, n + 1 + j] = (0,)
        middles[1 + j, n + 1 + i] = (0,)
    arrows = []
    vertices = 2 * n + 1
    for endpoints, labels in sorted(middles.items()):
        for _ in labels:
            a, b = endpoints
            arrows.extend(((a, vertices), (vertices, b)))
            vertices += 1
    return vertices, arrows


def all_paths(vertices, arrows):
    outgoing = defaultdict(list)
    for label, (a, b) in enumerate(arrows):
        outgoing[a].append((label, b))
    paths = []

    def extend(vertex, path):
        paths.append(path)
        for label, end in outgoing[vertex]:
            extend(end, (*path, label))

    for i in range(vertices):
        extend(i, (i,))
    return paths


def table(n, arrows, paths):
    counts = Counter((start, arrows[second][1]) for start, _, second in
                     (path for path in paths if len(path) == 3))
    return tuple(tuple(counts[i, j] for j in range(n + 1, 2 * n + 1))
                 for i in range(n + 1))


def path_sign(arrows, paths, vertex_image, explicit_arrows=None):
    if explicit_arrows is None:
        labels = {edge: i for i, edge in enumerate(arrows)}
        explicit_arrows = [labels[vertex_image[a], vertex_image[b]] for a, b in arrows]
    positions = {path: i for i, path in enumerate(paths)}
    images = [(vertex_image[path[0]], *(explicit_arrows[a] for a in path[1:]))
              for path in paths]
    order = tuple(positions[path] for path in images)
    assert len(set(order)) == len(paths)
    return sign(order)


def check_graphs():
    pair_checks = relabelings = middle_swaps = block_exchanges = graph_count = 0
    for n in range(1, 5):
        orders = tuple(permutations(range(n)))
        graphs = tuple(graph_edges(n))
        matrices = []
        for edges in graphs:
            vertices, arrows = make_quiver(n, edges)
            paths = all_paths(vertices, arrows)
            matrices.append(table(n, arrows, paths))
            assert len(paths) == 22 * n + 8 * len(edges) + 1
            assert Counter(arrow for path in paths for arrow in path[1:]) == {
                arrow: 2 for arrow in range(len(arrows))
            }
            path_count = len(paths)
            assert sign((*range(path_count, 2 * path_count), *range(path_count))) == -1
            block_exchanges += 1
            graph_count += 1
            middles = defaultdict(list)
            for (a, m), (mm, b) in zip(arrows[::2], arrows[1::2]):
                assert m == mm
                middles[a, b].append(m)
            for order in orders:
                if moved(edges, order) != edges:
                    continue
                im = [0, *(1+i for i in order), *(n+1+i for i in order)]
                im.extend([-1] * (vertices - len(im)))
                for (a, b), fibre in middles.items():
                    for old, new in zip(fibre, middles[im[a], im[b]], strict=True):
                        im[old] = new
                assert path_sign(arrows, paths, im) == 1
                relabelings += 1
            for fibre in middles.values():
                for a, b in zip(fibre, fibre[1:]):
                    im = list(range(vertices))
                    im[a], im[b] = im[b], im[a]
                    assert path_sign(arrows, paths, im) == 1
                    middle_swaps += 1
        if n > 3:
            continue
        for i, left in enumerate(graphs):
            for j, right in enumerate(graphs):
                graph_iso = any(moved(left, order) == right for order in orders)
                a, b = matrices[i], matrices[j]
                incidence_iso = any(
                    all(a[row][col] == b[row_order[row]][col_order[col]]
                        for row in range(n + 1) for col in range(n))
                    for row_order in ((0, *(1 + x for x in order)) for order in orders)
                    for col_order in orders
                )
                assert graph_iso == incidence_iso
                pair_checks += 1
    print(f"{graph_count} graphs, {pair_checks} pairwise incidence comparisons, "
          f"{relabelings} vertex relabelings, {middle_swaps} middle swaps, "
          f"{block_exchanges} odd block exchanges")


def check_chains():
    for p in (2, 3, 5, 7, 11):
        arrows = [(0, 1)] * (p - 1) + [(1, 2)] * (p - 1)
        paths = all_paths(3, arrows)
        assert len(paths) == p * p + 2
        assert all(sum(i in path[1:] for path in paths) == p for i in range(len(arrows)))
    print("5 sharp prime chains verified by direct path enumeration")


def check_parallel_fields():
    graph_cases = path_lifts = 0
    for q in (3, 5, 9, 13, 17):
        d = (q - 1) & -(q - 1)
        t = d - 1
        from_scalars = {i * d % (q - 1) for i in range(q - 1)}
        minus_one = (q - 1) // 2
        assert minus_one not in from_scalars
        with_exchange = from_scalars | {(i + minus_one) % (q - 1) for i in from_scalars}
        assert (q - 1) // len(from_scalars) == d
        assert (q - 1) // len(with_exchange) == d // 2
        for n in range(1, 4):
            for edges in graph_edges(n):
                vertices, base_arrows = make_quiver(n, edges)
                arrows = [edge for edge in base_arrows for _ in range(t)]
                paths = all_paths(vertices, arrows)
                assert len(paths) == 2 * n + 1 + d * d * (5 * n + 2 * len(edges))
                assert len(paths) % 2 == 1
                assert Counter(arrow for path in paths for arrow in path[1:]) == {
                    arrow: d for arrow in range(len(arrows))
                }
                old_counts = table(n, base_arrows, all_paths(vertices, base_arrows))
                expected = tuple(tuple(x * t * t for x in row) for row in old_counts)
                assert table(n, arrows, paths) == expected
                middles = defaultdict(list)
                for (a, m), (_, b) in zip(base_arrows[::2], base_arrows[1::2]):
                    middles[a, b].append(m)
                edge_labels = {edge: i for i, edge in enumerate(base_arrows)}
                for order in permutations(range(n)):
                    if moved(edges, order) != edges:
                        continue
                    image = [0, *(1+i for i in order), *(n+1+i for i in order)]
                    image.extend([-1] * (vertices - len(image)))
                    for (a, b), fibre in middles.items():
                        for old, new in zip(fibre, middles[image[a], image[b]], strict=True):
                            image[old] = new
                    lift = [edge_labels[image[a], image[b]] * t + k
                            for a, b in base_arrows for k in range(t)]
                    assert path_sign(arrows, paths, image, lift) == 1
                    path_lifts += 1
                graph_cases += 1
    print(f"{graph_cases} graph-field cases and {path_lifts} parallel-arrow path lifts")


if __name__ == "__main__":
    check_graphs()
    check_chains()
    check_parallel_fields()
