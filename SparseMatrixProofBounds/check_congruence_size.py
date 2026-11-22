"""Finite checks for the dense bordered-pencil construction. Field 4 uses x^2+x+1."""

from itertools import product


def add(a, b, k):
    return a ^ b if k == 4 else (a+b) % k


def neg(a, k):
    return a if k == 4 else -a % k


def mul(a, b, k):
    if k != 4:
        return a*b % k
    x = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    return x ^ 7 if x & 4 else x


def inv(a, k):
    return next(b for b in range(1, k) if mul(a, b, k) == 1)


def dot(a, b, k):
    v = 0
    for x, y in zip(a, b):
        v = add(v, mul(x, y, k), k)
    return v


def tr(a):
    return list(map(list, zip(*a)))


def mm(a, b, k):
    return [[dot(x, y, k) for y in tr(b)] for x in a]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def rank(a, k):
    a = [r.copy() for r in a]
    d = 0
    for j in range(len(a[0])):
        p = next((i for i in range(d, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[d], a[p] = a[p], a[d]
        for i in range(d+1, len(a)):
            v = neg(mul(a[i][j], inv(a[d][j], k), k), k)
            a[i] = [add(x, mul(v,y,k), k) for x,y in zip(a[i],a[d])]
        d += 1
    return d


def pencil(a, l, k):
    return [[add(x, neg(mul(l, y, k), k), k) for x,y in zip(r,s)]
            for r,s in zip(a,tr(a))]


def restriction(a):
    n = len(a)
    out = [[0]*(2*n) for _ in range(2*n)]
    for i,j,u,v in product(range(n), range(n), range(2), range(2)):
        z = mul(1 << u, mul(a[i][j], 1 << v, 4), 4)
        out[2*i+u][2*j+v] = z ^ mul(z,z,4)
    return out


def test(k,h):
    m = 2*h
    n = m+1
    c = 1; d = 2 if k == 4 else k-1
    norm = h % (2 if k == 4 else k)
    t = next(x for x in range(1,k) if x != mul(c, mul(d,norm,k), k))
    l = mul(c, inv(d,k),k)
    b = eye(n)
    b[-1][-1] = t
    for i in range(h):
        b[i][-1] = c
        b[-1][i] = d
    assert rank(b,k) == rank(pencil(b,l,k),k) == n
    a0 = [r.copy() for r in b]
    a0[0][h] = a0[h][0] = neg(1,k)
    r = eye(n)
    rest = [i for i in range(m) if i not in (0,h)]
    for i in rest[1:]:
        r[i][rest[0]] = 1
    a = mm(mm(r,a0,k),tr(r),k)
    partial = pencil(a,l,k)
    assert rank(a,k) == n and rank(partial,k) == n-1 and a != tr(a)
    assert all(a[i][j] for i in rest for j in rest if i!=j)
    sparse_columns = [[row[i] for i in (0,h,m)] for row in partial]
    assert rank(sparse_columns,k) == 2
    count = 0
    for i,j in product(range(h),range(h,m)):
        dst = [row.copy() for row in b]
        dst[i][j] = dst[j][i] = neg(1,k)
        perm = list(range(n))
        perm[i],perm[0] = perm[0],perm[i]
        perm[j],perm[h] = perm[h],perm[j]
        assert dst == [[a0[x][y] for y in perm] for x in perm]
        count += 1
    if k == 4:
        ar,br = restriction(a),restriction(b)
        assert rank(ar,2) == rank(br,2) == 2*n
        assert ar!=tr(ar) and br!=tr(br)
        assert rank(pencil(br,l,4),4) == 2*n
        ac = pencil(ar,l,4)
        six = [2*x+j for x in (0,h,m) for j in range(2)]
        assert rank([[row[j] for j in six] for row in ac],4) < 6
    return count


if __name__ == "__main__":
    cases = [(3,2),(3,4),(5,3),(5,4),(7,3),(4,2),(4,4)]
    total = sum(test(*case) for case in cases)
    print(f"Checked {len(cases)} bordered pencils, {total} completions and two binary trace restrictions.")
