"""Run uniform norm lifting in a monogenic algebra with hidden CRT components."""
from itertools import product

def polynomial_multiply(a, b, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return c

def remainder(a, f, p):
    c = list(a)
    for i in range(len(c) - 1, len(f) - 2, -1):
        if c[i]:
            for j, x in enumerate(f):
                c[i - len(f) + 1 + j] = (c[i - len(f) + 1 + j] - c[i] * x) % p if j < len(f) - 1 else 0
    return c[:len(f) - 1]

def irreducibles(p, d):
    divisors = [(*a, 1) for k in range(1, d // 2 + 1)
                for a in product(range(p), repeat=k)]
    found = []
    for a in product(range(p), repeat=d):
        f = (*a, 1)
        if a[0] and all(any(remainder(f, g, p)) for g in divisors):
            found.append(f)
            if len(found) == 2:
                return found
    raise AssertionError("fixture requires two irreducible factors")

def kernel(columns, p):
    rows = [list(row) for row in zip(*columns)]
    n = len(columns)
    pivots = []
    for j in range(n):
        k = len(pivots)
        choice = next((i for i in range(k, len(rows)) if rows[i][j]), None)
        if choice is None:
            continue
        rows[k], rows[choice] = rows[choice], rows[k]
        rows[k] = [x * pow(rows[k][j], -1, p) % p for x in rows[k]]
        for i, row in enumerate(rows):
            if i != k and row[j]:
                rows[i] = [(x - row[j] * y) % p for x, y in zip(row, rows[k])]
        pivots.append(j)
    for j in range(n):
        if j not in pivots:
            vec = [0] * n
            vec[j] = 1
            for k, pivot in enumerate(pivots):
                vec[pivot] = -rows[k][j] % p
            yield tuple(vec)

def split_off(n, ell):
    power = 1
    while n % ell == 0:
        n //= ell
        power *= ell
    return power, n

def primes(n):
    for ell in range(2, n + 1):
        if n % ell == 0:
            yield ell
            while n % ell == 0:
                n //= ell

class Algebra:
    def __init__(self, p, d, factors):
        self.p, self.d = p, d
        self.q, self.h = p**d, p - 1
        self.f = polynomial_multiply(*factors, p)
        self.n = len(self.f) - 1
        self.zero = self.scalar(0)
        self.one = self.scalar(1)
        self.basis = [tuple(int(i == j) for j in range(self.n)) for i in range(self.n)]

    def scalar(self, a):
        return (a % self.p,) + (0,) * (self.n - 1)

    def add(self, a, b):
        return tuple((x + y) % self.p for x, y in zip(a, b))

    def sub(self, a, b):
        return tuple((x - y) % self.p for x, y in zip(a, b))

    def mul(self, a, b):
        return tuple(remainder(polynomial_multiply(a, b, self.p), self.f, self.p))

    def power(self, a, e):
        assert e >= 0
        r = self.one
        while e:
            if e & 1:
                r = self.mul(r, a)
            a = self.mul(a, a)
            e //= 2
        return r

    def eq_mask(self, a, b):
        return self.sub(self.one, self.power(self.sub(a, b), self.h))

    def blend(self, masks, vals):
        total = self.zero
        for mask, value in zip(masks, vals):
            total = self.add(total, self.mul(mask, value))
        return total

    def sylow_scalar(self, ell, cofactor):
        for a in range(1, min(self.p, 1 + 3 * self.p.bit_length()**2)):
            if pow(a, self.h // ell, self.p) != 1:
                return self.scalar(pow(a, cofactor, self.p))
        raise AssertionError("nonresidue outside test window")

    def map_digits(self, z, g, u, ell, size, shift):
        r = self.one
        place = 1
        remaining = size
        while remaining > 1:
            remaining //= ell
            lhs = self.power(z, remaining)
            rhs = self.power(g, size // ell)
            masks = [self.eq_mask(lhs, self.power(rhs, j)) for j in range(ell)]
            assert self.blend(masks, [self.one] * ell) == self.one
            z = self.mul(z, self.blend(masks, [
                self.power(g, (-j * place) % size) for j in range(ell)]))
            if place < shift:
                assert masks[0] == self.one
            else:
                r = self.mul(r, self.blend(masks, [
                    self.power(u, j * (place // shift)) for j in range(ell)]))
            place *= ell
        assert z == self.one
        return r

    def fixed_ring_root(self, a, ell):
        size, m = split_off(self.h, ell)
        w = self.sylow_scalar(ell, m)
        primary = self.power(a, m * pow(m, -1, size))
        secondary = self.mul(a, self.power(primary, self.h - 1))
        r = self.map_digits(primary, w, w, ell, size, ell)
        return self.mul(r, self.power(secondary, pow(ell, -1, m)))

    def etale_root(self, a, ell):
        coeff = self.power(a, self.h // ell)
        columns = [self.sub(self.power(b, self.p), self.mul(coeff, b))
                   for b in self.basis]
        left = self.one
        c = self.zero
        for b in kernel(columns, self.p):
            support = self.power(b, self.q - 1)
            c = self.add(c, self.mul(self.mul(left, support), b))
            left = self.mul(left, self.sub(self.one, support))
        assert left == self.zero
        assert self.power(c, self.q - 1) == self.one
        assert self.power(c, self.p) == self.mul(coeff, c)
        y = self.mul(self.power(c, ell), self.power(a, self.q - 2))
        assert self.power(y, self.h // ell) == self.one
        root = self.mul(c, self.power(self.fixed_ring_root(y, ell), self.q - 2))
        assert self.power(root, ell) == a
        return root

    def norm_lift(self, a):
        ps = [ell for ell in primes(self.d) if self.h % ell == 0]
        scalar = self.scalar(a)
        s = (self.q - 1) // self.h
        h0 = self.h
        for ell in ps:
            _, h0 = split_off(h0, ell)
        cofactor = self.h // h0
        exp = cofactor * pow(cofactor, -1, h0) * pow(self.d, -1, h0)
        result = self.power(scalar, exp)
        for ell in ps:
            size, m = split_off(self.h, ell)
            z = self.power(scalar, m * pow(m, -1, size))
            u = self.sylow_scalar(ell, m)
            larger, _ = split_off(self.q - 1, ell)
            for _ in range((larger // size).bit_length()):
                if size == larger:
                    break
                u = self.etale_root(u, ell)
                size *= ell
            assert size == larger
            base = self.power(u, s)
            base_size, _ = split_off(self.h, ell)
            result = self.mul(result, self.map_digits(z, base, u, ell, base_size, 1))
        assert self.power(result, s) == scalar
        return result

def main():
    fixtures = [(2, 3), (3, 2), (3, 4), (3, 6), (5, 2), (5, 3),
                (7, 2), (7, 3), (7, 6), (13, 2), (13, 3), (19, 6)]
    cases = 0
    for p, d in fixtures:
        factors = irreducibles(p, d)
        algebra = Algebra(p, d, factors)
        for a in range(1, p):
            b = algebra.norm_lift(a)
            for f in factors:
                independent = Algebra(p, d, [f, (1,)])
                b_mod_f = tuple(remainder(b, f, p))
                assert independent.power(b_mod_f, (p**d - 1) // (p - 1)) == independent.scalar(a)
            cases += 1
    print(f"{cases} norm targets across {len(fixtures)} hidden-factor algebras verified")

if __name__ == "__main__":
    main()
