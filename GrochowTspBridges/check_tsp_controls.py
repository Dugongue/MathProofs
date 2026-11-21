"""Exact, standard-library controls for the metric, tensor and postman results."""

from itertools import combinations, product

from check_shortcuts import metric_dp


def metric_controls():
    # Each vertex is an L, R or D city. Relabeling all indices within a block
    # does not change a fixture, so one odd set of each size suffices.
    for labels, blocks, members in [(4, 1, {0}), (4, 1, {0, 1, 2}), (2, 2, {0})]:
        per_type = labels * blocks
        n = 3 * per_type

        def cost(a, b):
            a_type, a_label = divmod(a, per_type)
            b_type, b_label = divmod(b, per_type)
            if a_type == b_type == 0 and a_label // labels == b_label // labels:
                crosses = (a_label % labels in members) != (b_label % labels in members)
                return 1 + crosses
            if a_type == b_type == 1:
                return 1
            if b_type == 2 and a_type < 2 and a_label == b_label:
                return 1
            return 2

        edges = [(a, b, cost(a, b)) for a, b in combinations(range(n), 2)]
        assert metric_dp(n, edges, [3 * n] * n, 0, 0) == n + blocks

    forbidden_count = 0
    for mask in range(16):
        if mask.bit_count() % 2 == 0:
            continue
        points = []
        for city_type, i in product(range(3), range(4)):
            scale = 8 if city_type == 2 else 4
            coords = [scale * (j == i) for j in range(4)]
            height = (-4, 4, 0)[city_type]
            sign = (1 if mask & (1 << i) else -1) if city_type == 0 else 0
            points.append(coords + [height, sign])
        for a, b in combinations(range(12), 2):
            u, i = divmod(a, 4)
            v, j = divmod(b, 4)
            squared = sum((x - y) ** 2 for x, y in zip(points[a], points[b]))
            if u == v == 0:
                assert squared == (32 if (mask >> i ^ mask >> j) & 1 == 0 else 36)
            elif u == v == 1 or u == 1 and v == 2 and i == j:
                assert squared == 32
            elif u == 0 and v == 2 and i == j:
                assert squared == 33
            else:
                assert squared >= 64
                forbidden_count += 1
    assert forbidden_count == 368
    print("Metric TSP: single and replicated host optima, plus all 528 squared distances.")


def lifted_tours(shift):
    base = [(0, 1, 0), (1, 2, 0), (2, 3, 0), (3, 0, 1),
            (4, 5, 0), (5, 6, 0), (6, 7, 0), (7, 4, -1)]
    forward = [(u, v, change, 1) for u, v, change in base]
    forward.extend([(0, 5, shift, 2), (4, 1, 0, 2)])
    arcs = forward + [(v, u, -change, 8) for u, v, change, _ in forward]
    graph = [{} for _ in range(24)]
    for u, v, change, w in arcs:
        for s in range(3):
            graph[3 * u + s][3 * v + (s + change) % 3] = w
    tour_costs = []

    def traverse(v, seen, cost):
        if seen.bit_count() == 24:
            if 0 in graph[v]:
                tour_costs.append(cost + graph[v][0])
            return
        for u, weight in graph[v].items():
            if not seen & (1 << u):
                traverse(u, seen | (1 << u), cost + weight)

    traverse(0, 1, 0)
    return len(tour_costs), min(tour_costs)


def normalized_postman(n, interior, boundary, target, limit):
    edges = interior + boundary
    best = float("inf")
    for counts in product(*([(1, 2)] * len(interior) + [(0, 1, 2)] * len(boundary))):
        if sum(counts[len(interior):]) > limit:
            continue
        parity, voltage, cost = 0, 0, 0
        graph = [[] for _ in range(n)]
        for copies, (u, v, w, g) in zip(counts, edges):
            cost += copies * w
            if copies:
                graph[u].append(v)
                graph[v].append(u)
            if copies % 2:
                parity ^= (1 << u) | (1 << v)
                voltage ^= g
        if parity or voltage != target:
            continue
        reached = {0}
        queue = [0]
        for u in queue:
            for v in graph[u]:
                if v not in reached:
                    reached.add(v)
                    queue.append(v)
        if len(reached) == n:
            best = min(best, cost)
    return best


def postman_controls():
    stars = [(c, c + i, 2, 0) for c, i in product((0, 4), range(1, 4))]
    pairs = [(i, i + 4, 1, 0) for i in range(4)]
    assert normalized_postman(8, stars, pairs, 0, 8) == 16
    assert normalized_postman(8, stars, pairs, 0, 2) == 18
    mandatory = [(0, 1, 1, 0), (2, 3, 1, 0)]
    gains = [(0, 2, 3, g) for g in (0, 1, 2, 4, 8)]
    assert normalized_postman(4, mandatory, gains, 15, 10) == 16
    assert normalized_postman(4, mandatory, gains, 15, 3) == float("inf")
    print("Rural Postman: explicit metric-slack and cycle-rank fixtures reproduced.")


if __name__ == "__main__":
    metric_controls()
    first, second = lifted_tours(0), lifted_tours(1)
    assert (first, second) == ((6, 26), (2, 30))
    print("Lifted ATSP: exhaustive tour counts and minima are (6, 26) and (2, 30).")
    postman_controls()
