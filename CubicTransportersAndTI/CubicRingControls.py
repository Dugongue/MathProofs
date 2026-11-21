from itertools import product
from random import Random

rng = Random(1909)

def check(p, n):
    def add(x, y):
        return ((x % p + y % p) % p) + p * ((x // p + y // p) % p)
    def neg(x):
        return (-x % p) + p * (-(x // p) % p)
    def mul(x, y):
        return (x * y % p) + p * (((x % p) * (y // p) + (x // p) * (y % p)) % p)
    def power(x, n):
        z = 1
        for _ in range(n):
            z = mul(z, x)
        return z
    def inv(x):
        assert x % p
        return power(x, p * (p - 1) - 1)
    def det(m):
        a = [list(row) for row in m]
        d = 1
        for i in range(len(a)):
            k = next((k for k in range(i, len(a)) if a[k][i] % p), -1)
            if k < 0:
                raise ValueError("expected invertible")
            if k != i:
                a[k], a[i] = a[i], a[k]
                d = neg(d)
            d = mul(d, a[i][i])
            r = inv(a[i][i])
            for k in range(i + 1, len(a)):
                u = mul(a[k][i], r)
                if u:
                    for j in range(i, len(a)):
                        a[k][j] = add(a[k][j], neg(mul(u, a[i][j])))
        return d
    def algmul(x, y):
        z = [0] * n
        for i, j in product(range(n), repeat=2):
            if i+j < n:
                z[i+j] = add(z[i+j], mul(x[i], y[j]))
        return z
    def unit():
        return rng.randrange(1,p) + p*rng.randrange(p)
    def amat(k):
        out = [[[rng.randrange(p*p) for _ in range(n)] for _ in range(k)] for _ in range(k)]
        for i,j in product(range(k), repeat=2):
            if i==j:
                out[i][j][0] = unit()
            elif ((i<j) if k==2 else (i>j)):
                out[i][j][0] = 0
        return out
    def mat(columns):
        return list(zip(*columns))
    for _ in range(8):
        pm, qm = amat(2), amat(3)
        phi_e = [0, unit()] + [rng.randrange(p*p) for _ in range(n-2)]
        images = [[1]+[0]*(n-1)]
        for i in range(1,n):
            images.append(algmul(images[-1], phi_e))
        x = mat([[c for i in range(2) for c in algmul(pm[i][k], images[r])]
                 for k,r in product(range(2),range(n))])
        y = mat([[c for j in range(3) for c in algmul(images[r], qm[j][l])]
                 for l,r in product(range(3),range(n))])
        h = mat([[c for i,j in product(range(2),range(3))
                  for c in algmul(algmul(pm[i][k], images[r]), qm[j][l])]
                 for k,l,r in product(range(2),range(3),range(n))])
        dphi = det(mat(images))
        p0 = det([[pm[i][j][0] for j in range(2)] for i in range(2)])
        q0 = det([[qm[i][j][0] for j in range(3)] for i in range(3)])
        measured = mul(mul(det(x),det(y)),inv(det(h)))
        expected = inv(mul(dphi, power(mul(mul(p0,p0), q0),n)))
        assert measured == expected, (p,n,measured,expected)
    units = [u for u in range(p*p) if u % p]
    lhs = {mul(power(x,2*n),power(y,n)) for x,y in product(units,repeat=2)}
    rhs = {power(u,n) for u in units}
    assert lhs == rhs
    return len(rhs)

counts = {(p,n):check(p,n) for p,n in product((2,3,5),(2,3,4))}
print("72 direct cubic determinant matrix controls over dual-number base rings passed.")
print("Residual power image sizes:", counts)
