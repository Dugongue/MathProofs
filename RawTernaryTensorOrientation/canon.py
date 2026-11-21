"""Canonical invariant for raw ternary tensors in the cubic-graph family."""

from collections import deque
from itertools import product
from frame import recover


def parity(p):
    return sum(x > y for i, x in enumerate(p) for y in p[i+1:]) % 2


def detbit(matrix):
    a = [list(row) for row in matrix]
    bit = 0
    for i in range(len(a)):
        j = next(j for j in range(i, len(a)) if a[j][i] % 3)
        if i != j:
            a[i], a[j] = a[j], a[i]
            bit ^= 1
        u = a[i][i] % 3
        bit ^= int(u == 2)
        for j in range(i+1, len(a)):
            c = a[j][i] * u
            a[j] = [(x-c*y) % 3 for x, y in zip(a[j], a[i])]
    return bit


def xor_sum(left, right):
    return {a ^ b for a in left for b in right}


def gauge(weights, edges):
    rows = {}
    for color, pairs in enumerate(edges):
        for u, v in pairs:
            col = (1 << (3+u)) | (1 << (3+v)) | (1 << color)
            while col:
                p = col.bit_length() - 1
                if p not in rows:
                    rows[p] = col
                    break
                col ^= rows[p]
    v = weights << 3
    for p in sorted(rows, reverse=True):
        if p >= 3 and (v >> p) & 1:
            v ^= rows[p]
    signs = {v & 7}
    for p, row in rows.items():
        if p < 3:
            signs = xor_sum(signs, {0, row})
    return v >> 3, signs


def rooted(root, adj, weights):
    queue, order, ids = deque([root]), [], {root: 0}
    while queue:
        u = queue.popleft()
        order.append(u)
        for v in adj[u]:
            if v not in ids:
                ids[v] = len(ids)
                queue.append(v)
    pairs, labels = [], []
    for c in range(3):
        pairs.append([(i, ids[adj[u][c]]) for i, u in enumerate(order) if i < ids[adj[u][c]]])
        labels.append([order[i][c] for i, _ in pairs[c]])
    w = sum((weights[u] == 2) << i for i, u in enumerate(order))
    norm, signs = gauge(w, pairs)
    key = (tuple(tuple(block) for block in pairs), norm)
    local_perm = sum(parity(block) << c for c, block in enumerate(labels))
    return order, key, {s ^ local_perm for s in signs}


def graph_key(weights, frame_sign=0):
    adj = {u: [] for u in weights}
    for c in range(3):
        fibers = {}
        for u in weights:
            fibers.setdefault(u[c], []).append(u)
        if any(len(pair) != 2 for pair in fibers.values()):
            return None
        for u, v in fibers.values():
            adj[u].append(v)
            adj[v].append(u)
    for u, ns in adj.items():
        if len(set(ns)) < 3:
            return None
        walks = [w for v in ns for w in adj[v] if w != u]
        if len(set(walks)) != len(walks):
            return None
    rest, components = set(weights), []
    while rest:
        root = min(rest)
        vertices, key, tags = rooted(root, adj, weights)
        rest.difference_update(vertices)
        for other in vertices[1:]:
            _, candidate, signs = rooted(other, adj, weights)
            if candidate < key:
                key, tags = candidate, signs
            elif candidate == key:
                tags.update(signs)
        blocks = [sorted({u[c] for u in vertices}) for c in range(3)]
        components.append((key, tags, blocks))
    components.sort(key=lambda item: item[0])
    total = {frame_sign ^ sum(parity([j for _, _, b in components for j in b[c]]) << c
                              for c in range(3))}
    for i, (key, tags, blocks) in enumerate(components):
        total = xor_sum(total, tags)
        if i and key == components[i-1][0]:
            total = xor_sum(total, {0, sum((len(b) % 2) << c for c, b in enumerate(blocks))})
    return tuple(k for k, _, _ in components), min(total)


def transform(t, rows, axis):
    d = len(rows)
    out = {}
    for key in product(range(d), repeat=3):
        old = list(key)
        value = 0
        for j, coeff in enumerate(rows[key[axis]]):
            old[axis] = j
            value += coeff * t.get(tuple(old), 0)
        if value % 3:
            out[key] = value % 3
    return out


def canonical_key(t, d):
    """t maps index triples to coefficients, in ambient shape (d,d,d), d > 0."""
    if d <= 0 or any(len(key) != 3 or any(j not in range(d) for j in key) for key in t):
        raise ValueError("Invalid ternary tensor shape")
    data = dict(t)
    orientation = 0
    for c in range(3):
        # Circular ordering puts the contraction coordinate last.
        def coefficient(i, j, k):
            args = (k, i, j)
            return data.get(args[-c:] + args[:-c] if c else args, 0)
        pencil = [[[coefficient(i, j, k) for k in range(d)] for j in range(d)] for i in range(d)]
        lines = recover(pencil)
        if lines is None:
            return None
        orientation ^= detbit(lines) << c
        data = transform(data, lines, c)
    if any(len({u[c] for u in data}) != d for c in range(3)):
        return None
    return graph_key(data, orientation)
