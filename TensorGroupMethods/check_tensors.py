from fractions import Fraction
from itertools import combinations, product
from collections import deque


def row_chart(matrix, pivots, p=None):
    r = len(matrix)
    work = [list(map(Fraction, row)) if p is None else [x % p for x in row] for row in matrix]

    def inverse(x):
        return 1 / x if p is None else pow(x, -1, p)

    def reduce(x):
        return x if p is None else x % p

    for i, j in enumerate(pivots):
        pivot = next((k for k in range(i, r) if work[k][j]), None)
        if pivot is None:
            return None
        work[i], work[pivot] = work[pivot], work[i]
        weight = inverse(work[i][j])
        work[i] = [reduce(weight * x) for x in work[i]]
        for k in range(r):
            if i != k:
                coefficient = work[k][j]
                work[k] = [reduce(a - coefficient * b) for a, b in zip(work[k], work[i])]
    return work


def support_test(a, b, pivots, p=None):
    if a is None:
        return None
    n = len(a[0])
    adjacency = [[] for _ in range(n)]
    killed = []
    for i, pivot in enumerate(pivots):
        for j in sorted(set(range(n)) - set(pivots)):
            left, right = a[i][j], b[i][j]
            if right and not left:
                return None
            if left and not right:
                killed.append((pivot, j))
            if right:
                ratio = right / left if p is None else (right * pow(left, -1, p)) % p
                back = 1 / ratio if p is None else pow(ratio, -1, p)
                adjacency[pivot].append((j, ratio))
                adjacency[j].append((pivot, back))

    component = [-1] * n
    gamma = [0] * n
    counter = 0
    for root in range(n):
        if component[root] >= 0:
            continue
        component[root] = counter
        gamma[root] = Fraction(1) if p is None else 1
        queue = deque([root])
        while queue:
            u = queue.popleft()
            for v, ratio in adjacency[u]:
                value = gamma[u] * ratio
                if p is not None:
                    value %= p
                if component[v] < 0:
                    component[v], gamma[v] = counter, value
                    queue.append(v)
                elif gamma[v] != value:
                    return None
        counter += 1

    arcs = [set() for _ in range(counter)]
    indegree = [0] * counter
    for i, j in killed:
        u, v = component[i], component[j]
        if v not in arcs[u]:
            arcs[u].add(v)
            indegree[v] += 1
    queue = deque(i for i, degree in enumerate(indegree) if degree == 0)
    order = []
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in arcs[u]:
            indegree[v] -= 1
            if indegree[v] == 0:
                queue.append(v)
    if len(order) != counter:
        return None
    weights = {u: w for w, u in enumerate(order)}
    return gamma, tuple(weights[u] for u in component)


def exhaust_toric_cells():
    p = 3
    matrices = [(a, b, c, d) for a, b, c, d in product(range(p), repeat=4)
                if (a or c) and (b or d)]
    place = ((0, 2), (0, 3), (1, 2), (1, 3))
    weights = list(product(range(4), repeat=4))
    constants = list(product((1, 2), repeat=4))
    for entries in matrices:
        matrix = ((1, 0, *entries[:2]), (0, 1, *entries[2:]))
        witness_limits = set()
        for w in weights:
            difference = [w[j] - w[i] for i, j in place]
            if any(v and d < 0 for v, d in zip(entries, difference)):
                continue
            for g in constants:
                witness_limits.add(tuple((v * g[i] * pow(g[j], -1, p)) % p if d == 0 else 0
                                         for v, d, (i, j) in zip(entries, difference, place)))
        for target in matrices:
            target_m = ((1, 0, *target[:2]), (0, 1, *target[2:]))
            actual = support_test(matrix, target_m, (0, 1), p)
            assert (actual is not None) == (target in witness_limits)
    return len(matrices)**2


def gale_example():
    h = [[1, 0, 1, 2, -1, 7], [0, 1, 1, 1, 1, 1]]
    c = [[-1, -1, 1, 0, 0, 0], [-2, -1, 0, 1, 0, 0],
         [1, -1, 0, 0, 1, 0], [-7, -1, 0, 0, 0, 1]]
    d = [c[0], c[1], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]
    tau = [0, 2, 1, 4, 3, 5]
    permuted = [[row[i] for i in tau] for row in c]
    assert all(sum(x * y for x, y in zip(a, b)) == 0 for a in c for b in h)
    pivots = (2, 3, 4, 5)
    for source in (c, permuted):
        start = row_chart(source, pivots)
        gamma, weights = support_test(start, d, pivots)
        for i, pivot in enumerate(pivots):
            for j, a in enumerate(start[i]):
                diff = weights[j] - weights[pivot]
                if a:
                    assert diff >= 0
                limit = a * gamma[j] / gamma[pivot] if diff == 0 else 0
                assert limit == d[i][j]
    assert support_test(row_chart(c, pivots), row_chart(permuted, pivots), pivots) is None


def connected(vertices, edges):
    if not vertices:
        return False
    reached = {min(vertices)}
    previous = -1
    while len(reached) != previous:
        previous = len(reached)
        for u, v in edges:
            if u in reached:
                reached.add(v)
            if v in reached:
                reached.add(u)
    return reached == vertices


def induced_tree(vertices, edges):
    kept = [(u, v) for u, v in edges if u in vertices and v in vertices]
    return len(kept) == len(vertices) - 1 and connected(vertices, kept)


def test_graphic():
    checked = 0
    for n in range(2, 6):
        vertices = set(range(n))
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [pair for i, pair in enumerate(pairs) if mask >> i & 1]
            if not connected(vertices, edges):
                continue
            has_tree_partition = False
            for k in range(1, n):
                for side_tuple in combinations(range(n), k):
                    side = set(side_tuple)
                    if induced_tree(side, edges) and induced_tree(vertices - side, edges):
                        has_tree_partition = True
            incidence = [[int(u == i) - int(v == i) for u, v in edges] for i in range(n - 1)]
            edge_set = set(range(len(edges)))
            matroid_condition = any(
                all(row_chart(incidence, a + (b,), 2) is not None for b in edge_set - set(a))
                for a in combinations(range(len(edges)), n - 2)
            )
            assert has_tree_partition == matroid_condition
            checked += 1
    return checked


if __name__ == "__main__":
    print(f"Checked {exhaust_toric_cells()} labelled torus comparisons over F3.")
    gale_example()
    print("Both rational Gale-dual degenerations verified without labelled orbit equality.")
    print(f"Graphic condition agreed with induced-tree partition on {test_graphic()} connected graphs.")
