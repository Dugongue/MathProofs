from itertools import combinations, permutations, product
from random import Random
from canon import canonical_key, detbit, graph_key, parity, transform
from frame import recover
from pad import pad


def heawood():
    return [(i, 7+(i+s) % 7, c) for i in range(7) for c, s in enumerate((0, 1, 3))]


def truncated():
    k4 = [(0, 1, 0), (2, 3, 0), (0, 2, 1), (1, 3, 1), (0, 3, 2), (1, 2, 2)]
    edges = [(3*u+c, 3*v+c, c) for u, v, c in k4]
    return edges + [(3*v+a, 3*v+b, 3-a-b) for v in range(4)
                    for a, b in combinations(range(3), 2)]


def tensor(edges):
    labels = {}
    for c in range(3):
        for i, (u, v, _) in enumerate(e for e in edges if e[2] == c):
            for x in (u, v):
                labels[x, c] = i
    return {tuple(labels[x, c] for c in range(3)): 1 for x in range(2*len(edges)//3)}


def check_minors(t, d):
    tested = 0
    for axis in range(3):
        positions = {(u[(axis+1)%3], u[(axis+2)%3]): u[axis] for u in t}
        for i, j in combinations(range(d), 2):
            found = False
            for selected in combinations([rc for rc, x in positions.items() if x in (i, j)], 3):
                rows, cols = zip(*selected)
                if len(set(rows)) < 3 or len(set(cols)) < 3:
                    continue
                matches = sum(all((r, c) in positions for r, c in zip(rows, p))
                              for p in permutations(cols))
                found |= matches == 1
            assert found
            tested += 1
    return tested


def scramble(t, d, rng):
    for axis in range(3):
        rows = [[int(i == j) for j in range(d)] for i in range(d)]
        for _ in range(4*d):
            a, b = rng.sample(range(d), 2)
            rows[a] = [(x+y) % 3 for x, y in zip(rows[a], rows[b])]
        assert detbit(rows) == 0
        t = transform(t, rows, axis)
    return t


def brute_sign_image(t, d):
    """Independent control via every edge-sign assignment and every possible root image."""
    vertices = sorted(t)
    links = [[] for _ in vertices]
    incidence = []
    for c in range(3):
        for i in range(d):
            a, b = [j for j, u in enumerate(vertices) if u[c] == i]
            links[a].append(b)
            links[b].append(a)
            incidence.append((1 << a) | (1 << b) | (1 << (len(t)+c)))
    images = {0}
    for col in incidence:
        images.update({v ^ col for v in images})
    answer = set()
    for target in range(len(t)):
        assignment, pending = {0: target}, [0]
        consistent = True
        while pending:
            a = pending.pop()
            for b, dst in zip(links[a], links[assignment[a]]):
                if b not in assignment:
                    assignment[b] = dst
                    pending.append(b)
                consistent &= assignment[b] == dst
        if not consistent or len(set(assignment.values())) != len(t):
            continue
        flips = sum((t[v] != t[vertices[assignment[j]]]) << j for j, v in enumerate(vertices))
        perm_sign = 0
        for c in range(3):
            perm = {v[c]: vertices[assignment[j]][c] for j, v in enumerate(vertices)}
            perm_sign |= parity([perm[i] for i in range(d)]) << c
        answer.update(s ^ perm_sign for s in range(8) if flips | (s << len(t)) in images)
    return answer


if __name__ == "__main__":
    rng = Random(703)
    for edges in (truncated(), heawood()):
        t = tensor(edges)
        d = len(edges)//3
        for u in t:
            t[u] = rng.choice((1, 2))
        pair_count = check_minors(t, d)
        ref = graph_key(t)
        assert canonical_key(scramble(t, d, rng), d) == ref
        stabilizer = brute_sign_image(t, d)
        distinct = set()
        for mask in range(8):
            changed = {u: (w * (-1)**sum(((mask >> c) & 1) * (u[c] == 0)
                                          for c in range(3))) % 3 for u, w in t.items()}
            key = graph_key(changed)
            assert key == graph_key(t, mask)
            assert (key == ref) == (mask in stabilizer)
            if mask == 1:
                assert canonical_key(scramble(changed, d, rng), d) == key
            distinct.add(key[1])
        print(d, "edges per colour,", pair_count, "mixed-minor certificates,", len(distinct),
              "signed orbits among eight reflection choices; dense basis replay passed", flush=True)
    t = tensor(heawood())
    t[min(t)] = 2
    h = brute_sign_image(t, 7)
    assert 7 not in h
    doubled = {**t, **{tuple(i+7 for i in u): w for u, w in t.items()}}
    for mask in range(8):
        assert (graph_key(doubled, mask) == graph_key(doubled)) == (mask in h or mask ^ 7 in h)
    print("Repeated odd-size component swap verified.")
    d = 4
    diagonal = [[[int(i == j == k) for k in range(d)] for j in range(d)] for i in range(d)]
    assert recover(diagonal) is None
    print("Diagonal obstruction confirmed.")
    # Companion action of t modulo the irreducible t^3 - t - 1.
    # This polynomial has no root in F3. Its companion has order 13.
    def move(v):
        a, b, c = v
        return c, (a+c) % 3, b
    vectors = list(product(range(3), repeat=3))
    assert any(move(v) != v for v in vectors)
    for v in vectors:
        u = v
        for _ in range(13):
            u = move(u)
        assert u == v
    print("Order-13 stabilizer control passed on all 27 vectors.")
    for shape in ((0, 0, 0), (2, 3, 1), (16, 4, 3), (17, 2, 9), (49, 1, 1)):
        original = {(0, 0, 0): 2} if all(shape) else {}
        padded, raw = pad(shape, original)
        from math import isqrt
        k = isqrt(padded[0]-shape[0])
        assert k % 2 == 0 and k*k > max(shape)
        assert padded == tuple(n+k*k for n in shape)
        assert len(raw) == len(original)+k**3
        marker = {tuple(i-n for i, n in zip(key, shape)): v
                  for key, v in raw.items() if key not in original}
        def evaluate(x, y, z):
            return sum(w*x[i]*y[j]*z[l] for (i, j, l), w in marker.items()) % 3
        for _ in range(8):
            x, y, z = [[rng.randrange(3) for _ in range(k*k)] for _ in range(3)]
            # P = I + E01, so PX adds row 1 to row 0; ZP^-1 subtracts column 0 from column 1.
            px, zp = x.copy(), z.copy()
            for i in range(k):
                px[i] += x[k+i]
                zp[k*i+1] -= z[k*i]
            assert evaluate(px, y, zp) == evaluate(x, y, z)
    print("Five padding shapes and 40 trace-action controls passed.")
