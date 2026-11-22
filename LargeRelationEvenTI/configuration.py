"""Exact controls for the graph incidence sign gadget and cyclic relation family."""

from itertools import combinations, combinations_with_replacement, permutations, product


def edge(u, v):
    return tuple(sorted((u, v)))


def two_token_graph(vertices, edges):
    nodes = list(combinations_with_replacement(vertices, 2))
    links = set()
    for a, b in nodes:
        for u, v in edges:
            for old, new in ((u, v), (v, u)):
                if old == a:
                    links.add(edge((a, b), edge(new, b)))
                if old == b:
                    links.add(edge((a, b), edge(a, new)))
    return nodes, sorted(links)


def finite_records(nodes, links, reference):
    """Tuple (site, selected edge endpoints, attached torsor bit)."""
    words = set()
    for i, v in enumerate(nodes):
        incident = [e for e in links if v in e]
        for assignment in product(range(2), repeat=len(incident)):
            ports = frozenset(zip(incident, assignment))
            words.add((v, ports, (sum(assignment) + reference[i]) % 2))
    return words


def sign(perm):
    return sum(a > b for a, b in combinations(perm, 2)) % 2


def check_lifts():
    base = (0, 1, 2)
    nodes, links = two_token_graph(base, list(combinations(base, 2)))
    source_words = finite_records(nodes, links, [0]*len(nodes))
    boundaries = {}
    for flips in product(range(2), repeat=len(links)):
        boundary = tuple(sum(x for e, x in zip(links, flips) if v in e) % 2
                         for v in nodes)
        boundaries.setdefault(boundary, dict(zip(links, flips)))
    assert len(boundaries) == 2**(len(nodes)-1)
    assert all(sum(bits) % 2 == 0 for bits in boundaries)
    cases = witnesses = 0
    for sizes in ((1, 1, 1), (1, 1, 2), (1, 2, 3)):
        for perm in permutations(base):
            sites = {s: edge(perm[s[0]], perm[s[1]]) for s in nodes}
            edges = {e: edge(sites[e[0]], sites[e[1]]) for e in links}
            for internal in product(range(2), repeat=len(base)):
                action = {}
                for a, b in nodes:
                    if a == b:
                        action[a, b] = internal[a]
                    else:
                        action[a, b] = int(perm[a] > perm[b]) * (sizes[a]*sizes[b] % 2)
                # A direct permutation on the concatenated raw coordinates.
                with_positions = [(perm[i], j) for i in base for j in range(sizes[i])]
                rank = {p: i for i, p in enumerate(sorted(with_positions))}
                combined = (sign([rank[p] for p in with_positions]) + sum(internal)) % 2
                for twist in range(2):
                    target_reference = [twist] + [0]*(len(nodes)-1)
                    boundary = tuple(action[v] ^ target_reference[nodes.index(sites[v])]
                                     for v in nodes)
                    expected = combined == twist
                    assert (boundary in boundaries) == expected
                    cases += 1
                    if not expected:
                        continue
                    flips = boundaries[boundary]
                    target_words = finite_records(nodes, links, target_reference)
                    transported = {
                        (sites[v], frozenset((edges[e], s ^ flips[e]) for e, s in ports),
                         bit ^ action[v])
                        for v, ports, bit in source_words
                    }
                    assert transported == target_words
                    witnesses += 1
    return cases, witnesses


def check_cycles():
    comparisons = 0
    for n in range(18, 51, 4):
        vertices = range(n)
        edges = sorted({edge(v, (v+d) % n) for v in vertices for d in (1, 3)})
        neighbors = [{b if a == v else a for a, b in edges if v in (a, b)}
                     for v in vertices]
        assert all(len(s) == 4 for s in neighbors)
        assert len(set(map(frozenset, neighbors))) == n
        for d in (1, 3):
            walks = sum(d in neighbors[y] for x in neighbors[0] for y in neighbors[x])
            assert walks == {1: 12, 3: 10}[d]
        for shift in vertices:
            for direction in (1, -1):
                vertex_map = [(shift+direction*v) % n for v in vertices]
                edge_map = [edges.index(edge(vertex_map[a], vertex_map[b])) for a, b in edges]
                assert sign(edge_map) == 0
                comparisons += 1
    return comparisons


if __name__ == "__main__":
    cases, witnesses = check_lifts()
    print(f"{cases} exact lift decisions, {witnesses} incidence-record bijections")
    print(f"{check_cycles()} even dihedral edge actions across nine cyclic examples")
