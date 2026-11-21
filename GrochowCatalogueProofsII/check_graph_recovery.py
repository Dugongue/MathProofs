"""Finite controls for path separation and adaptive group multiplication recovery."""
from itertools import combinations, permutations, product
from random import Random


def rooted_walk_widths(order, edges):
    """Return widths of integer-line homomorphisms sending vertex zero to zero."""
    reached = {0}
    parents = []
    while len(reached) < order:
        new = [(a, b) for a, b in edges if (a in reached) != (b in reached)]
        if not new:
            return
        a, b = new[0]
        if b in reached:
            a, b = b, a
        parents.append((a, b))
        reached.add(b)
    for steps in product((-1, 1), repeat=order - 1):
        height = [0] * order
        for (parent, vertex), step in zip(parents, steps):
            height[vertex] = height[parent] + step
        if all(abs(height[a] - height[b]) == 1 for a, b in edges):
            yield max(height) - min(height)


def path_difference(m, widths):
    return sum(
        max(0, m - w) + max(0, m + 2 - w) - 2 * max(0, m + 1 - w)
        for w in widths
    )


def test_paths():
    patterns = 0
    for m in range(1, 5):
        for order in range(1, m + 2):
            available = tuple(combinations(range(order), 2))
            for size in range(len(available) + 1):
                for edges in combinations(available, size):
                    widths = list(rooted_walk_widths(order, edges))
                    if widths:
                        assert path_difference(m, widths) == 0
                        patterns += 1
        path = tuple((i, i + 1) for i in range(m + 1))
        assert path_difference(m, rooted_walk_widths(m + 2, path)) == 2
    return patterns


def recover(n, query):
    identity = query(0, 0)
    columns = {query(0, j): j for j in range(n)}
    rows = {query(i, 0): i for i in range(n)}
    labels = tuple(columns)
    assert set(columns) == set(rows)
    trivial = {a: a for a in labels}
    left = {identity: trivial}
    right = {identity: trivial}

    def extend(a, known_opposite, use_row):
        unassigned = set(labels)
        result = {}
        while unassigned:
            b = min(unassigned)
            ab = query(rows[a], columns[b]) if use_row else query(rows[b], columns[a])
            for permutation in known_opposite.values():
                result[permutation[b]] = permutation[ab]
                unassigned.discard(permutation[b])
        return result

    def closure(permutation_cache, a, action):
        actions = tuple(permutation_cache.values()) + (action,)
        waiting = list(permutation_cache)
        while waiting:
            b = waiting.pop()
            for generator in actions:
                successor = generator[b]
                if successor not in permutation_cache:
                    permutation_cache[successor] = {
                        x: generator[permutation_cache[b][x]] for x in labels
                    }
                    waiting.append(successor)
        assert a in permutation_cache

    while len(left) < n:
        a = min(set(labels) - set(left))
        new_left = extend(a, right, True)
        new_right = extend(a, left, False)
        closure(left, a, new_left)
        closure(right, a, new_right)
        assert set(left) == set(right)
    return left, identity


def test_groups():
    rng = Random(349)
    tested = []
    for degree in (2, 3, 4, 5):
        group = list(permutations(range(degree)))
        index = {p: i for i, p in enumerate(group)}
        n = len(group)
        mult = [[index[tuple(g[h[i]] for i in range(degree))] for h in group] for g in group]
        inverse = [row.index(0) for row in mult]
        rows = rng.sample(range(n), n)
        columns = rng.sample(range(n), n)
        names = rng.sample(range(100 * n), n)
        decode = {name: i for i, name in enumerate(names)}
        queried = set()

        def query(i, j):
            queried.add((i, j))
            return names[mult[inverse[rows[i]]][columns[j]]]

        table, identity = recover(n, query)
        anchor = decode[identity]
        for a, b in product(table, repeat=2):
            rhs = names[mult[mult[decode[a]][inverse[anchor]]][decode[b]]]
            assert table[a][b] == rhs
        assert len(queried) <= 6 * n - 1
        tested.append((f"S{degree}", n, len(queried)))
    return tested


if __name__ == "__main__":
    print("Nonzero connected path controls:", test_paths())
    print("Group, group size, distinct cross entries:", test_groups())
