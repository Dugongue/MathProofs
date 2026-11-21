"""Differential controls for the shortcut-tree oracle. Python 3.10+."""

from itertools import combinations, product
from math import inf
from random import Random


def path_entries(lengths, skipped, visited):
    m = len(lengths)
    distance = [0]
    for length in lengths:
        distance.append(distance[-1] + length)
    change = [0]
    for u, v in zip(skipped, visited):
        change.append(change[-1] + v - u)
    left = [2 * distance[i] + change[i] for i in range(m)]
    right = [2 * (distance[-1] - distance[j]) + change[-1] - change[j - 1]
             for j in range(1, m + 1)]
    best_prefix = inf
    split = inf
    for lcost, rcost in zip(left, right):
        best_prefix = min(best_prefix, lcost)
        split = min(split, best_prefix + rcost)
    base = sum(skipped)
    full = sum(visited)
    return (base, base + min(left), base + min(right), base + split,
            full + distance[-1], full + 2 * distance[-1])


def preprocess(n, tree, penalties, anchors):
    neighbors = [[] for _ in range(n)]
    for u, v, length in tree:
        neighbors[u].append((v, length))
        neighbors[v].append((u, length))
    root = min(anchors)
    order = [root]
    parent = {root: None}
    children = [[] for _ in range(n)]
    for u in order:
        for v, length in neighbors[u]:
            if v != parent[u]:
                children[u].append((v, length))
                parent[v] = u
                order.append(v)

    core = set(anchors)
    for u in reversed(order[1:]):
        if u in core:
            core.add(parent[u])
    nodes = anchors | {u for u in core
                       if sum(v in core for v, _ in neighbors[u]) >= 3}
    skip = penalties.copy()
    visit = [0] * n
    paths = []
    for u in reversed(order):
        for v, length in children[u]:
            if v not in core:
                skip[u] += skip[v]
                visit[u] += min(skip[v], 2 * length + visit[v])
    for u in sorted(nodes):
        for v, weight in children[u]:
            if v in core:
                lengths = [weight]
                skipped, visited = [], []
                while v not in nodes:
                    skipped.append(skip[v])
                    visited.append(visit[v])
                    [(v, weight)] = [(j, w) for j, w in children[v] if j in core]
                    lengths.append(weight)
                paths.append((u, v, path_entries(lengths, skipped, visited)))
    fees = {u: (skip[u], visit[u]) for u in nodes}
    return fees, paths


class Components:
    def __init__(self, vertices):
        self.parent = {x: x for x in vertices}
        self.count = len(self.parent)

    def root(self, x):
        while self.parent[x] != x:
            x = self.parent[x]
        return x

    def join(self, x, y):
        x, y = self.root(x), self.root(y)
        if x == y:
            return False
        self.parent[x] = y
        self.count -= 1
        return True


def best_connections(active, edges, start, finish):
    # Each edge has the schema (left, right, odd surcharge, even surcharge).
    forest = Components(active)
    children = {v: [] for v in active}
    chords = []
    for i, (u, v, _, _) in enumerate(edges):
        if forest.join(u, v):
            children[u].append((v, i))
            children[v].append((u, i))
        else:
            chords.append(i)
    if forest.count != 1:
        return inf

    order = [(start, None, None)]
    for u, pred, _ in order:
        order.extend((v, u, i) for v, i in children[u] if v != pred)
    candidates = sorted(edges, key=lambda edge: edge[3])
    optimum = inf
    for bits in product((0, 1), repeat=len(chords)):
        odd = [i for i, bit in zip(chords, bits) if bit]
        boundary = {start, finish} if start != finish else set()
        for i in odd:
            u, v, _, _ = edges[i]
            boundary.symmetric_difference_update((u, v))
        for u, pred, i in reversed(order[1:]):
            if u in boundary:
                odd.append(i)
                boundary.symmetric_difference_update((u, pred))
        assert not boundary

        groups = Components(active)
        cost = 0
        for i in odd:
            u, v, odd_cost, _ = edges[i]
            groups.join(u, v)
            cost += odd_cost
        for u, v, _, even_cost in candidates:
            if groups.join(u, v):
                cost += even_cost
        assert groups.count == 1
        optimum = min(optimum, cost)
    return optimum


def edited_value(tables, shortcuts, start, finish):
    fees, paths = tables
    fixed = {start, finish}
    choices = sorted(set(fees) - fixed)
    result = inf
    for flags in product((0, 1), repeat=len(choices)):
        active = fixed | {v for v, flag in zip(choices, flags) if flag}
        base = sum(pair[v in active] for v, pair in fees.items())
        edges = []
        for u, v, costs in paths:
            state = (u in active) + 2 * (v in active)
            base += costs[state]
            if state == 3:
                edges.append((u, v, costs[4] - costs[3], costs[5] - costs[3]))
        edges.extend((u, v, w, 2 * w) for u, v, w in shortcuts
                     if u in active and v in active)
        result = min(result, base + best_connections(active, edges, start, finish))
    return result


def metric_dp(n, edges, penalties, start, finish):
    """Independent baseline. Optimize every possible collection of visits."""
    dist = [[inf] * n for _ in range(n)]
    for i in range(n):
        dist[i][i] = 0
    for u, v, w in edges:
        dist[u][v] = dist[v][u] = min(dist[u][v], w)
    for k, i, j in product(range(n), repeat=3):
        dist[i][j] = min(dist[i][j], dist[i][k] + dist[k][j])
    other = [v for v in range(n) if v not in {start, finish}]
    states = [{v: inf for v in range(n)} for _ in range(1 << len(other))]
    states[0][start] = 0
    answer = inf
    for mask, costs in enumerate(states):
        missing = sum(penalties[v] for i, v in enumerate(other) if not mask & (1 << i))
        for u, cost in costs.items():
            if cost == inf:
                continue
            answer = min(answer, cost + dist[u][finish] + missing)
            for i, v in enumerate(other):
                bit = 1 << i
                if not mask & bit:
                    future = states[mask | bit]
                    future[v] = min(future[v], cost + dist[u][v])
    return answer


def check():
    for lengths, expected in [((1, 1, 4), 6), ((2, 2, 2), 7)]:
        tree = [(i, i + 1, w) for i, w in enumerate(lengths)]
        penalties = [20] * 4
        shortcuts = [(0, 3, 1)]
        tables = preprocess(4, tree, penalties, {0, 3})
        assert edited_value(tables, shortcuts, 0, 0) == expected
        assert metric_dp(4, tree + shortcuts, penalties, 0, 0) == expected

    rng = Random(19017)
    counts = {"closed": 0, "open": 0}
    for _ in range(180):
        n = rng.randrange(1, 9)
        tree = [(rng.randrange(u), u, rng.randrange(7)) for u in range(1, n)]
        anchors = set(rng.sample(range(n), rng.randrange(1, n + 1)))
        penalty_choices = [0, 1, 3, 7, 16, 1 + 2 * sum(w for _, _, w in tree)]
        penalties = rng.choices(penalty_choices, k=n)
        tables = preprocess(n, tree, penalties, anchors)
        pairs = list(combinations(sorted(anchors), 2))
        for closed in (True, False):
            start = rng.choice(sorted(anchors))
            finish = start if closed or not pairs else rng.choice(sorted(anchors - {start}))
            shortcuts = [(u, v, rng.randrange(9))
                         for u, v in rng.choices(pairs, k=rng.randrange(5))] if pairs else []
            actual = edited_value(tables, shortcuts, start, finish)
            expected = metric_dp(n, tree + shortcuts, penalties, start, finish)
            assert actual == expected, (tree, penalties, anchors, shortcuts, start, finish)
            counts["closed" if start == finish else "open"] += 1
    print(f"Matched independent exact optima on {counts['closed']} closed and "
          f"{counts['open']} open queries, plus both longest-edge fixtures.")


if __name__ == "__main__":
    check()
