"""Finite controls for the edge toggle and small-prime signature constructions."""
from itertools import product
from math import isqrt

def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]

def transpose(a):
    return list(map(list, zip(*a)))

def multiply(a, b, p):
    return [[sum(x * y for x, y in zip(row, column)) % p
             for column in zip(*b)] for row in a]

def diagonal(entries):
    return [[value if i == j else 0 for j in range(len(entries))]
            for i, value in enumerate(entries)]

def toggle_test(p, n, edges, charges):
    squares = {a * a % p for a in range(p)}
    nu = next(a for a in range(1, p) if a not in squares)
    a, b = next((a, b) for a, b in product(range(p), repeat=2)
                if (a * a + b * b) % p == nu)
    k = [[a, b], [-b, a]]
    ki = [[pow(nu, -1, p) * x % p for x in row] for row in transpose(k)]
    swap = [[0, 1], [1, 0]]
    matchings = []
    for e in edges:
        for group in matchings:
            if all(not set(e).intersection(f) for f in group):
                group.append(e)
                break
        else:
            matchings.append([e])
    charges_sign = [(-1)**c for c in charges]
    target = diagonal([nu**c for c in charges])

    cases = 0
    for values in product([1, -1], repeat=len(edges)):
        signs = dict(zip(edges, values))
        indicators = [0] * n
        x, y = identity(n), identity(n)
        for group in matchings:
            forward, reverse = identity(n), identity(n)
            for u, v in group:
                if signs[u, v] == 1:
                    continue
                pair = indicators[u], indicators[v]
                block, inv = { (0, 0): (k, ki), (1, 1): (ki, k),
                              (0, 1): (swap, swap), (1, 0): (swap, swap) }[pair]
                for i, left in enumerate((u, v)):
                    for j, right in enumerate((u, v)):
                        forward[left][right] = block[i][j]
                        reverse[left][right] = inv[i][j]
                indicators[u] ^= 1
                indicators[v] ^= 1
            x, y = multiply(forward, x, p), multiply(y, reverse, p)

        # Column permutation of X and the corresponding row permutation of Y.
        permutation = [(j + 1) % n for j in range(n)]
        xp = [[row[j] for j in permutation] for row in x]
        yp = [y[j] for j in permutation]
        assert multiply(xp, yp, p) == identity(n)
        assert multiply(yp, xp, p) == identity(n)
        gram = multiply(xp, transpose(xp), p)
        assert gram == diagonal([nu**a for a in indicators])
        vertex_signs = [1] * n
        for (u, v), sign in signs.items():
            vertex_signs[u] *= sign
            vertex_signs[v] *= sign
        scale = (1 - nu) * pow(2, -1, p)
        assert [[(gram[i][j] - target[i][j]) % p for j in range(n)]
                for i in range(n)] == diagonal([
                    scale * (s - c) % p for s, c in zip(vertex_signs, charges_sign)])
        cases += 1
    return cases

def signature_test():
    values = [2, 3, 6, 5, 180, -1, -5]
    modulus = 4
    for a in values:
        modulus *= abs(a)
    limit = 3 * modulus.bit_length()**2
    primes = [p for p in range(3, limit + 1, 2) if modulus % p
              and all(p % t for t in range(2, isqrt(p) + 1))]
    for bits in product([0, 1], repeat=len(values)):
        a = 1
        for value, take in zip(values, bits):
            if take:
                a *= value
        square = a > 0 and isqrt(a)**2 == a
        assert square == all(pow(a % p, (p - 1) // 2, p) == 1 for p in primes)
    return 2**len(values), len(primes)

if __name__ == "__main__":
    graph = [(u, v) for u in range(3) for v in range(3, 6)]
    cases = sum(toggle_test(p, 6, graph, [1, 0, 0, 0, 0, 0])
                for p in (3, 5, 7, 13))
    products, prime_count = signature_test()
    print(f"{cases} edge assignments and {products} square-class products over "
          f"{prime_count} admissible primes checked")
