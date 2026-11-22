"""Sparse FGS augmentations, induced transporters and row-endomorphism checks.

Indices are zero based. Fresh coordinates are appended inside the named first
part, a fixed basis ordering of the same FGS identity blocks.
"""
from collections import defaultdict
from dataclasses import dataclass


@dataclass
class Tensor:
    parts: list
    entries: set  # All nonzero coefficients in these examples equal one.


def size(parts):
    return sum(map(len, parts))


def parts_with_anchor(n):
    return [list(range(n)), [n]]


def shape(t):
    return tuple(map(size, t.parts))


def check_map(source, target, maps):
    assert shape(source) == shape(target)
    for p, q, f in zip(source.parts, target.parts, maps):
        assert [sorted(f[i] for i in group) for group in p] == [sorted(group) for group in q]
    assert {(maps[0][i], maps[1][j], maps[2][k]) for i,j,k in source.entries} == target.entries


def augment(t, order):
    row, col, sl = order
    parts = [[list(group) for group in axis] for axis in t.parts]
    nr, nc = size(parts[row]), size(parts[col])
    unit = 1+min(nr,nc)
    entries = set(t.entries)
    fresh_cols = {}
    for k, group in enumerate(parts[sl]):
        for copy in range(unit << k):
            parts[row][0].append(nr)
            for index in group:
                triple = [0,0,0]
                triple[row], triple[col], triple[sl] = nr, nc, index
                entries.add(tuple(triple))
                parts[col][0].append(nc)
                fresh_cols[k,copy,index] = nc
                nc += 1
            nr += 1
    parts[sl] = [list(range(size(parts[sl])))]
    return Tensor(parts,entries), fresh_cols


def extend(source, target, maps, order):
    left, lc = augment(source,order)
    right, rc = augment(target,order)
    extended = [m + list(range(len(m),d)) for m,d in zip(maps,shape(left))]
    row, col, sl = order
    for (k,copy,i), a in lc.items():
        extended[col][a] = rc[k,copy,maps[sl][i]]
    check_map(left,right,extended)
    return left,right,extended


def block_variables(parts, start):
    # Only entries of maps respecting the surviving partitions are unknowns.
    lookup = {}
    for group in parts:
        for i in group:
            for j in group:
                lookup[i,j] = start
                start += 1
    return lookup, start


def row_rank(equations, prime, offset=0):
    pivots = {}
    for eq in equations:
        row = {k:v % prime for k,v in eq.items() if k >= offset and v % prime}
        while row:
            p = min(row)
            if p not in pivots:
                inv = pow(row[p],-1,prime)
                pivots[p] = {j:a*inv % prime for j,a in row.items()}
                break
            factor = row[p]
            for j,v in pivots[p].items():
                a = (row.get(j,0)-factor*v) % prime
                if a:
                    row[j] = a
                else:
                    row.pop(j,None)
    return len(pivots)


def row_end_dimension(t, order, prime):
    row, col, sl = order
    row_vars, cut = block_variables(t.parts[row],0)
    col_vars, _ = block_variables(t.parts[col],cut)
    left = defaultdict(list)
    right = defaultdict(list)
    for (i,j), v in row_vars.items():
        left[j].append((i,v))
    for (i,j), v in col_vars.items():
        right[i].append((j,v))
    equations = defaultdict(lambda: defaultdict(int))
    for triple in t.entries:
        i,j,k = triple[row],triple[col],triple[sl]
        for h,var in left[i]:
            equations[k,h,j][var] += 1
        for h,var in right[j]:
            equations[k,i,h][var] -= 1
    # Dimension of the row projection of the kernel of L A_i - A_i Q.
    return cut-row_rank(equations.values(),prime)+row_rank(equations.values(),prime,cut)


def lie(n, edges):
    m = len(edges)
    N = 3*m+n
    entries = {(i,i,i % m) for i in range(3*m)}
    for f,(u,v) in enumerate(edges):
        entries.update((3*m+j,3*m+j,f) for j in (u,v))
    entries.update((i,i,m) for i in range(N+1))
    return Tensor([parts_with_anchor(N),parts_with_anchor(N),parts_with_anchor(m)],entries)


def algebra(n,edges):
    arcs = [(u,v) for x,y in edges for u,v in ((x,y),(y,x))]
    d = n+len(arcs)
    entries = {(i,i,i) for i in range(n)}
    for j,(u,v) in enumerate(arcs,n):
        entries.update(((u,j,j),(j,v,j)))
    for i in range(d):
        entries.update(((d,i,i),(i,d,i)))
    return Tensor([parts_with_anchor(d),parts_with_anchor(d),[list(range(d))]],entries)


def run():
    checks = 0
    for n,edges,perm in [(3,[(0,1),(1,2)],[1,2,0]),(4,[(0,1),(1,2)],[3,1,0,2])]:
        m = len(edges)
        new = sorted(tuple(sorted((perm[u],perm[v]))) for u,v in edges)
        edge_map = [new.index(tuple(sorted((perm[u],perm[v])))) for u,v in edges]
        source, target = lie(n,edges),lie(n,new)
        p = [j*m+i for j in range(3) for i in edge_map]+[3*m+i for i in perm]+[3*m+n]
        maps = [p,p,edge_map+[m]]
        check_map(source,target,maps)
        for stage,order in enumerate(((0,1,2),(2,0,1),(1,2,0))):
            if stage:
                for prime in (2,3,5):
                    assert row_end_dimension(source,order,prime) == 1
                    checks += 1
            source,target,maps = extend(source,target,maps,order)

        source,target = algebra(n,edges),algebra(n,new)
        def arcs(es):
            return [(u,v) for a,b in es for u,v in ((a,b),(b,a))]
        new_arcs = arcs(new)
        p = perm+[n+new_arcs.index((perm[u],perm[v])) for u,v in arcs(edges)]
        maps = [p+[len(p)],p+[len(p)],p]
        check_map(source,target,maps)
        for order in ((2,0,1),(1,2,0)):
            for prime in (2,3,5):
                assert row_end_dimension(source,order,prime) == 1
                checks += 1
            source,target,maps = extend(source,target,maps,order)
    # An injective pencil whose first two matrices do not commute. The free
    # coefficient axis is first in this specialization of the one-link layout.
    m,n = 3,3
    entries = {(0,0,1),(1,1,0),(2,0,0)}
    entries.update((m,i,i) for i in range(n+1))
    source = Tensor([parts_with_anchor(m),parts_with_anchor(n),parts_with_anchor(n)],entries)
    maps = [[2,0,1,m],[1,2,0,n],[1,2,0,n]]
    target = Tensor(source.parts,{tuple(maps[i][v] for i,v in enumerate(t)) for t in entries})
    for order in ((0,1,2),(2,0,1),(1,2,0)):
        for prime in (2,3,5):
            assert row_end_dimension(source,order,prime)==1
            checks += 1
        source,target,maps = extend(source,target,maps,order)
    print(f"{checks} row-endomorphism dimensions equal one over the three fields; "
          "all thirteen successive FGS tensor transporter checks passed.")


if __name__ == "__main__":
    run()
