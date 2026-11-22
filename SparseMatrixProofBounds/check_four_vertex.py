"""Verify the block-diagonal assignments by exact finite-field elimination."""

from check_congruence_size import add, eye, inv, mm, mul, neg, tr


def solve(a, rhs, k):
    n = len(a[0])
    rows = [row + [y] for row, y in zip(a, rhs)]
    pivots = []
    for j in range(n):
        d = len(pivots)
        i = next((s for s in range(d,len(rows)) if rows[s][j]), None)
        if i is None:
            continue
        rows[d],rows[i] = rows[i],rows[d]
        v = inv(rows[d][j],k)
        rows[d] = [mul(x,v,k) for x in rows[d]]
        for i in range(len(rows)):
            if i==d or not rows[i][j]:
                continue
            v = neg(rows[i][j],k)
            rows[i] = [add(x,mul(v,y,k),k) for x,y in zip(rows[i],rows[d])]
        pivots.append(j)
    assert all(not r[-1] for r in rows[len(pivots):])
    sol = [0]*n
    for i,j in enumerate(pivots):
        sol[j] = rows[i][-1]
    return len(pivots),sol


def split_count(total, p):
    if total%p:
        return [total]
    return [p+1,total-p-1]


def check(k):
    p = 2 if k==4 else k
    sizes = [1,2,3]
    source = [(d,5*p+1) for d in sizes]+[(3,p+1)]*6
    targets = [(d,r) for (d,c),g in zip(source[:2],(6,0))
               for r in split_count(c+g,p)]
    total = source[2][1] + 6*(p+1) - 2
    targets += [(3,p+1)] + [(3,r) for r in split_count(total-p-1,p)]
    assert all(c>=2 and c%p for _,c in source+targets)
    assert sum(d*c for d,c in source)==sum(d*c for d,c in targets)
    anchors = [i for i,(d,_) in enumerate(targets) if d==3]
    lam = next(x for x in range(1,k) if mul(x,x,k)==neg(1,k))
    forms = {d:[[int(i==j or j==i+1) for j in range(d)] for i in range(d)] for d in sizes}
    maps = {}
    for j,(r,_) in enumerate(targets):
        gram = [[0]*r for _ in range(r)]
        for a,(c,count) in enumerate(source):
            x = [[0]*c for _ in range(r)]
            if a<3:
                if c==r:
                    x = eye(r)
            else:
                h = (a-3)//2
                if j==anchors[0] or h==0:
                    x = [[int(i==y) for y in range(c)] for i in range(r)]
                elif j==anchors[1]:
                    x = ([[i if i==y else 0 for y in range(c)] for i in range(r)]
                         if h==1 else [[int((i+1)%c==y) for y in range(c)] for i in range(r)])
                if (a-3)%2:
                    x = [[mul(v,lam,k) for v in row] for row in x]
            maps[j,a]=x
            value = mm(mm(x,forms[c],k),tr(x),k)
            gram = [[add(v,mul(count%p,w,k),k) for v,w in zip(u,z)] for u,z in zip(gram,value)]
        assert gram==forms[r]
    edges = [(a,j,u,v) for j,(r,_) in enumerate(targets)
             for a,(c,_) in enumerate(source) for u in range(c) for v in range(r)]
    coeff,rhs=[],[]
    for j,(r,count) in enumerate(targets):
        for i in range(r):
            for h in range(r):
                coeff.append([maps[j,a][i][u] if jj==j and v==h else 0 for a,jj,u,v in edges])
                rhs.append(count%p if i==h else 0)
    for a,(c,count) in enumerate(source):
        for i in range(c):
            for h in range(c):
                coeff.append([maps[j,a][v][h] if aa==a and u==i else 0 for aa,j,u,v in edges])
                rhs.append(count%p if i==h else 0)
    dimension,z = solve(coeff,rhs,k)
    assert dimension==len(coeff)-1
    assert mm(coeff,[[v] for v in z],k)==[[t] for t in rhs]
    return len(coeff)


if __name__ == "__main__":
    count = sum(check(k) for k in (4,5,13,17))
    print(f"Verified mismatched three-type core assignments over four fields with {count} inverse-component equations.")
