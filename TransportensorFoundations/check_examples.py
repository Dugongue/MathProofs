"""Exhaustive checks of two examples in the Transportensor specification."""
from itertools import product

def cycle_count(modulus, edges):
    n = len(edges)
    # Directed simple cycle, with its two oppositely directed arcs if n=2.
    group = set()
    for shift in range(n):
        for g in product(range(1, modulus), repeat=n):
            if all(g[(i+1)%n]*edges[i]%modulus == edges[(i+shift)%n]*g[i]%modulus for i in range(n)):
                group.add((shift,g))
    return group

def compose(f, g, q):
    a, x = f
    b, y = g
    n = len(x)
    return ((a+b)%n, tuple(x[(i+b)%n]*y[i]%q for i in range(n)))

def binary_apply(cols, v):
    z = 0
    for i,c in enumerate(cols):
        if v & (1<<i):
            z ^= c
    return z

def invertible(n, cols=(), span=frozenset([0])):
    if len(cols)==n:
        yield cols
        return
    for v in range(1,1<<n):
        if v not in span:
            yield from invertible(n, cols+(v,), span | {u^v for u in span})

def quadratic(v):
    return ((v & 3) & (v>>2)).bit_count()%2

def polar(v,w):
    return quadratic(v^w)^quadratic(v)^quadratic(w)

def marker_check():
    V = range(16)
    result = [[],[]]
    for m in invertible(4):
        if any((binary_apply(m,v)&3)!=binary_apply(m,v&3) for v in V):
            continue
        q_ok = all(quadratic(binary_apply(m,v))==quadratic(v) for v in V)
        b_ok = all(polar(binary_apply(m,1<<i),binary_apply(m,1<<j))==polar(1<<i,1<<j)
                   for i in range(4) for j in range(4))
        if q_ok: result[0].append(m[:2])
        if b_ok: result[1].append(m[:2])
    gl = set(invertible(2))
    for entries in result:
        assert set(entries)==gl and len(entries)==len(gl)==6

if __name__ == "__main__":
    group = cycle_count(3, [1,2])
    assert len(group)==4
    for g in group:
        if g[0]==1:
            assert compose(g,g,3)==(0,(2,2))
    marker_check()
    print("Four automorphisms of the signed two-cycle; both rotation lifts have order four.")
    print("Binary projector padding: six distinct restrictions and six lifts for each of Sp and quadratic O.")
