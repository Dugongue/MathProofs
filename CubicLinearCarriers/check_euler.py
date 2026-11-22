"""Coefficient linear algebra for the polar-preimage test over the prime field."""
from itertools import combinations_with_replacement


def column_basis(columns):
    pivots = {}
    for vector in columns:
        row = [v % 3 for v in vector]
        for i in sorted(pivots):
            scale = row[i]
            if scale:
                row = [(a-scale*b) % 3 for a, b in zip(row, pivots[i])]
        lead = next((i for i, a in enumerate(row) if a), None)
        if lead is not None:
            pivots[lead] = [a*row[lead] % 3 for a in row]
    return len(pivots)


def check_cycle(m):
    n = 2*m
    terms = list(combinations_with_replacement(range(n), 3))
    index = {t: i for i, t in enumerate(terms)}
    f = [(i, i, m+i) for i in range(m)] + [(i, (i+1) % m, m+i) for i in range(m)]
    columns = []
    for a in range(n):
        for b in range(n):
            v = [0]*len(terms)
            for t in f:
                for j, x in enumerate(t):
                    if x == a:
                        changed = list(t)
                        changed[j] = b
                        v[index[tuple(sorted(changed))]] += 1
            columns.append(v)
    mixed = [i for i, t in enumerate(terms) if t[0] != t[-1]]
    return n*n-column_basis(columns), n*n-column_basis(([v[i] for i in mixed] for v in columns))


if __name__ == "__main__":
    for m in range(4, 9):
        assert check_cycle(m) == (1, 1)
    from fiber import fiber_tensor, refinement_mark, decolor, Tensor
    from groups import Field, identity, substitute
    from functools import cache

    # Recover the marks in two fields, including after a dense change of basis.
    for k in (Field((0, 1)), Field((1, 0, 1))):
        k.add, k.mul = cache(k.add), cache(k.mul)
        m, n = 4, 8
        cubic = {}
        for i in range(m):
            for t in [(i, i, i+m), (i, (i+1) % m, i+m)]:
                cubic[tuple(sorted(t))] = 1
        assert refinement_mark(k, n, cubic) == (0,)*n
        h = identity(n)
        for offset in (1, 3):
            for i in range(n):
                j = (i+offset) % n
                a = 3 if k.e > 1 else 2
                h[i] = [k.add(x, k.mul(a,y)) for x,y in zip(h[i],h[j])]
        for axis in range(n):
            for c in range(1, k.q):
                form = dict(cubic)
                form[(axis,)*3] = k.power(c, 3)
                changed = substitute(k, form, h)
                mark = tuple(k.mul(c, x) for x in h[axis])
                assert refinement_mark(k, n, changed) == mark
        tensor = fiber_tensor(k, n, changed)
        assert tuple(tensor.entry(i, 2*n, n) for i in range(n)) == mark
        assert tensor.entry(2*n, 2*n, n) == 1 and all(len(axis) == 1 for axis in tensor.parts)
        assert refinement_mark(k, 2, {(0,0,1):1}) is None
        print(f"F_{k.q}: all {n*(k.q-1)} transported marked refinements recovered; "
              f"ordinary tensor shape {tensor.shape}.")
    # Check every entry of a one-stage rank-marker example against literal rectangles.
    small = Tensor(((1,1),(1,),(1,)), lambda x,y,z: 2 if x == 1 else 0)
    out = decolor(small, 0)
    expected = {(1,0,0):2}
    row, col = 2, 1
    for j in range(4):
        rank, layer = 4*(2**j), j+1
        expected[row,0,layer] = expected[j//2,col,layer] = 1
        for v in range(rank):
            expected[row+1+v,col+1+v,layer] = 1
        row += 1+rank
        col += 1+rank
    assert out.shape == (row,col,5)
    for i in range(row):
        for j in range(col):
            for z in range(5):
                assert out.entry(i,j,z) == expected.get((i,j,z),0)
    print(f"All {row*col*5} entries of an independent decoloring fixture agreed.")
