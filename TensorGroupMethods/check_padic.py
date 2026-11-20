"""Finite checks for stabilizer counts and uneven-precision p-adic search."""
from itertools import product
import random
from math import factorial


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def product_matrix(a, b, modulus):
    return [[sum(x * y for x, y in zip(row, column)) % modulus
             for column in zip(*b)] for row in a]


def valuation(value, prime):
    assert value
    power = 0
    while value % prime == 0:
        value //= prime
        power += 1
    return power


def exp_scaled(x, prime, s, r):
    modulus = prime**r
    n = len(x)
    total = identity(n)
    power = identity(n)
    for k in range(1, r + 2):
        power = product_matrix(power, x, modulus)
        denom = factorial(k)
        loss = valuation(denom, prime)
        coefficient = prime**(s*k-loss) * pow(denom//prime**loss, -1, modulus)
        total = [[(old + coefficient * new) % modulus for old, new in zip(a, b)]
                 for a, b in zip(total, power)]
    return total


def inverse_near(g, prime, s, r):
    modulus = prime**r
    n = len(g)
    one = identity(n)
    change = [[(one[i][j]-g[i][j]) % modulus for j in range(n)] for i in range(n)]
    power = identity(n)
    total = identity(n)
    for _ in range(1, r//s+1):
        power = product_matrix(power, change, modulus)
        total = [[(x+y) % modulus for x, y in zip(a,b)] for a,b in zip(total,power)]
    return total


def conjugate(diagonal, g, inverse, modulus):
    scaled = [[g[i][j]*diagonal[j] for j in range(len(g))] for i in range(len(g))]
    return product_matrix(scaled, inverse, modulus)


def search(diagonal, target, prime, s, r):
    n = len(diagonal)
    slots = [(i, j, valuation(b-a, prime), b-a) for i, a in enumerate(diagonal)
             for j, b in enumerate(diagonal) if a != b]
    e = max(k for _, _, k, _ in slots)
    assert s >= e + 2
    w = []
    for i, j, v, diff in slots:
        if target[i][j] % prime**min(r, s+v):
            return False
        precision = max(0, r-s-v)
        modulus = prime**precision
        w.append(target[i][j]//prime**(s+v) * pow(diff//prime**v, -1, modulus) % modulus
                 if precision else 0)

    def evaluate(z, magnitude):
        modulus = prime**magnitude
        x = [[0]*n for _ in range(n)]
        for (i, j, _, _), value in zip(slots, z):
            x[i][j] = value
        g = exp_scaled(x, prime, s, magnitude)
        g_inverse = exp_scaled([[-v for v in row] for row in x], prime, s, magnitude)
        return conjugate(diagonal, g, g_inverse, modulus)

    coordinate_modulus = prime**(r-s)
    z = [0]*len(slots)
    for _ in range(r-s+1):
        out = evaluate(z, r+e)
        f = [out[i][j]//prime**(s+v) * pow(diff//prime**v, -1, coordinate_modulus)
             % coordinate_modulus if coordinate_modulus > 1 else 0 for i,j,v,diff in slots]
        z = [(want + old - found) % coordinate_modulus for want, old, found in zip(w,z,f)]
    return target == evaluate(z, r)


def control(prime):
    s, r = 3, 5
    diag = [0, prime]
    modulus = prime**r
    fibers = {}
    for entries in product(range(prime**(r-s)), repeat=4):
        g = [[(int(i == j)+prime**s*entries[2*i+j]) % modulus for j in range(2)]
             for i in range(2)]
        t = conjugate(diag,g,inverse_near(g,prime,s,r),modulus)
        key = tuple(map(tuple,t))
        fibers[key] = fibers.get(key,0)+1
    bound = prime**(2*(r-s)+2*min(1,r-s))
    assert set(fibers.values()) == {bound}
    for t in fibers:
        target = [list(row) for row in t]
        assert search(diag,target,prime,s,r)
        target[0][0] = (target[0][0]+1) % modulus
        assert not search(diag,target,prime,s,r)
    return len(fibers), bound


if __name__ == "__main__":
    for p in (2,3):
        orbit_size, fiber = control(p)
        print(f"Fibre and search checks at p={p}: {orbit_size} local targets, {fiber} witnesses per target.")
    diag, p, s, r = [0,1,2], 2, 3, 6
    rng = random.Random(14)
    for _ in range(32):
        g = [[int(i==j)+p**s*rng.randrange(p**(r-s)) for j in range(3)] for i in range(3)]
        t = conjugate(diag,g,inverse_near(g,p,s,r),p**r)
        assert search(diag,t,p,s,r)
        t[2][2] = (t[2][2]+p**(r-1)) % p**r
        assert not search(diag,t,p,s,r)
    print("32 positive and 32 negative checks with unequal Smith precisions passed.")

