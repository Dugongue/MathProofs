"""Finite diagnostics for the singular anchor and cut-rank proofs."""
from itertools import product


def mm(a, b, q):
    return [[sum(x*y for x,y in zip(row, col)) % q for col in zip(*b)] for row in a]


def tensor(a, b):
    return [[x*y for x in row for y in brow] for row in a for brow in b]


def partial(a, n, q, first):
    if first:
        return [[sum(a[i*n+k][j*n+k] for k in range(n)) % q for j in range(n)]
                for i in range(n)]
    return [[sum(a[k*n+i][k*n+j] for k in range(n)) % q for j in range(n)]
            for i in range(n)]


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def covariance(q, n):
    s = [identity(n)[i] for i in range(n)]
    s[0][1] = 1
    inverse = identity(n)
    inverse[0][1] = -1
    basis = []
    for i, j in product(range(n), repeat=2):
        if i != j:
            a = [[0]*n for _ in range(n)]
            a[i][j] = 1
            basis.append(a)
    for i in range(n-1):
        a = [[0]*n for _ in range(n)]
        a[i][i], a[-1][-1] = 1, -1
        basis.append(a)
    size = n*n
    t = [[0]*size for _ in range(size)]
    for i, a in enumerate(basis):
        block = tensor(a, basis[(i+1) % len(basis)])
        t = [[(x+y) % q for x,y in zip(row,brow)] for row,brow in zip(t,block)]
    transport = tensor(s, identity(n))
    back = tensor(inverse, identity(n))
    moved = mm(mm(transport,t,q),back,q)
    u,v = mm(t,t,q),mm(moved,moved,q)
    assert partial(v,n,q,True) == mm(mm(s,partial(u,n,q,True),q),inverse,q)
    assert partial(v,n,q,False) == partial(u,n,q,False)
    if q == 2:
        assert sum(partial(u,n,q,True)[i][i] for i in range(n)) % q == 0


def anchor(q):
    for u, z in product(range(q), repeat=2):
        g = [[1,0,-z],[u,1,0],[0,0,1]]
        h = [[1,0],[z,1]]
        for x, y in product(product(range(q), repeat=3), product(range(q), repeat=2)):
            gx = mm(g,[[a] for a in x],q)
            hy = mm(h,[[a] for a in y],q)
            assert (gx[0][0]*hy[0][0] + gx[2][0]*hy[1][0]) % q == (x[0]*y[0]+x[2]*y[1]) % q


def gaussian(n, k, q):
    if not 0 <= k <= n:
        return 0
    numerator, denominator = 1,1
    for i in range(k):
        numerator *= q**(n-i)-1
        denominator *= q**(k-i)-1
    return numerator//denominator


def moment_truncations(q):
    for n in range(1,9):
        for r in range(9):
            partial_sum = sum((-1)**i*q**(i*(i-1)//2)*gaussian(n,i,q) for i in range(r+1))
            assert partial_sum == (-1)**r*q**(r*(r+1)//2)*gaussian(n-1,r,q)


if __name__ == "__main__":
    for q,n in ((2,2),(2,3),(3,3),(5,3)):
        covariance(q,n)
    for q in (2,3,5):
        anchor(q)
        moment_truncations(q)
    print("PASS: trace covariance, singular anchor extension, and Gaussian truncations.")
