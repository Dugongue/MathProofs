"""Check the generated-section GI reduction against exhaustive binary fiber isomorphisms."""
from itertools import permutations, product
from random import Random

# Vectors in F2^2 are the integers 0..3; matrices are pairs of column vectors.
GL = [(a, b) for a in (1, 2, 3) for b in (1, 2, 3) if a != b]
I = (1, 2)
def act(m, v):
    return (m[0] if v & 1 else 0) ^ (m[1] if v & 2 else 0)
def mul(m, n):
    return tuple(act(m, x) for x in n)
def inv(m):
    return next(x for x in GL if mul(m, x) == I)
def packed(columns):
    return sum(v << (2*i) for i, v in enumerate(columns))
def make_basis(constants, edges):
    n = len(constants)
    sections, span = [], {0}
    def retain(s):
        z = packed(s)
        if z not in span:
            sections.append(s)
            span.update([x ^ z for x in span])
    retain(constants)
    for s in sections:  # Unary propagation, including newly independent sections.
        for color in sorted({c for _, _, c, _ in edges}):
            t = [0]*n
            for u, v, c, m in edges:
                if c == color:
                    t[v] ^= act(m, s[u])
            retain(t)
    frames = []
    for v in range(n):
        first = next((s[v] for s in sections if s[v]), 0)
        second = next((s[v] for s in sections if s[v] not in (0, first)), 0)
        if not first or not second:
            return None
        frames.append((first, second))
    return frames
def transform(x, p, gauges):
    c, edges = x
    out = [0]*len(p)
    for i, v in enumerate(p):
        out[v] = act(gauges[i], c[i])
    return out, sorted((p[u],p[v],color,mul(gauges[v],mul(m,inv(gauges[u]))))
                       for u,v,color,m in edges)
def compare(x, y):
    n = len(x[0])
    bx, by = make_basis(*x), make_basis(*y)
    brute = {(p,g) for p in permutations(range(n)) for g in product(GL, repeat=n)
             if transform(x,p,g) == y}
    if bx is None or by is None:
        assert not brute or (bx is None and by is None)
        return False
    fast = set()
    for p in permutations(range(n)):
        g = tuple(mul(by[p[i]],inv(bx[i])) for i in range(n))
        if transform(x,p,g) == y:
            fast.add((p,g))
    assert brute == fast
    return True
if __name__ == "__main__":
    rng = Random(18374)
    trials = 0
    for _ in range(32):
        c = [1,1]
        edges = [(0,1,0,(2,0)), (1,0,0,(2,0))]
        edges += [(rng.randrange(2), rng.randrange(2), 1, (rng.randrange(4),rng.randrange(4))) for _ in range(3)]
        x = c, sorted(edges)
        p = rng.choice([(0,1),(1,0)])
        g = tuple(rng.choice(GL) for _ in p)
        y = transform(x,p,g)
        trials += compare(x,y)
        changed = (y[0], sorted(y[1]+[(0,0,2,(1,1))]))
        trials += compare(x,changed)
    print(trials, "pairs passed exhaustive comparison of all graph and fiber witnesses")
