"""Construct the two sparse multiplication tables for a small characteristic-spectrum example."""
from collections import Counter
from itertools import product


def build_graph(n, edges, primes, charge):
    adjacency = []
    colors = []

    def vertex():
        adjacency.append(set())
        return len(adjacency) - 1

    def connect(u, v):
        assert u != v and v not in adjacency[u]
        adjacency[u].add(v)
        adjacency[v].add(u)

    for p in primes:
        values = {}
        scopes = [[] for _ in range(n)]
        for i, j in edges:
            for edge in [(i, j), (j, i)]:
                values[edge] = [vertex() for _ in range(p)]
                colors.append(values[edge])
                scopes[edge[0]].append(edge)
        constraints = [(scope, charge) for scope in scopes]
        constraints.extend(([(i, j), (j, i)], 0) for i, j in edges)
        for scope, total in constraints:
            assert scope
            fiber = []
            for head in product(range(p), repeat=len(scope) - 1):
                labels = head + ((total - sum(head)) % p,)
                node = vertex()
                fiber.append(node)
                for edge, label in zip(scope, labels):
                    connect(node, values[edge][label])
            colors.append(fiber)
    anchors = []
    for i, members in enumerate(colors):
        anchor = vertex()
        if anchors:
            connect(anchors[-1], anchor)
        anchors.append(anchor)
        for u in members:
            connect(u, anchor)
        connect(anchor, vertex())
        if i == 0:
            connect(anchor, vertex())
    return adjacency, anchors


def multiplication_table(graph):
    """Yield (left input, right input, output) for each coefficient equal to one."""
    next_index = len(graph)
    for i, neighbors in enumerate(graph):
        yield i, i, i
        for j in sorted(neighbors):
            arrow = next_index
            next_index += 1
            yield i, arrow, arrow
            yield arrow, j, arrow


def refine(graph):
    labels = [0] * len(graph)
    while True:
        signatures = [(labels[i], tuple(sorted(labels[j] for j in row)))
                      for i, row in enumerate(graph)]
        classes = {s: i for i, s in enumerate(sorted(set(signatures)))}
        updated = [classes[s] for s in signatures]
        if len(set(updated)) == len(set(labels)):
            return updated
        labels = updated


def main():
    n = 7
    edges = sorted({tuple(sorted((i, (i + j) % n))) for i in range(n) for j in [1, 2]})
    for charge in (0, 1):
        graph, anchors = build_graph(n, edges, [2, 3], charge)
        entries = list(multiplication_table(graph))
        labels = refine(graph)
        counts = Counter(labels)
        assert len(graph) == 652 and sum(map(len, graph)) == 3542
        assert len(anchors) == 98 and all(counts[labels[a]] == 1 for a in anchors)
        assert len(set(entries)) == len(entries) == 7736
        assert max(max(entry) for entry in entries) + 1 == 4194
    print("Both tensors have side 4194 and 7736 nonzero coefficients; all 98 anchors are distinguished.")


if __name__ == "__main__":
    main()
