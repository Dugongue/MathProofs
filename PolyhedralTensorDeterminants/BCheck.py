from itertools import product
from math import gcd, prod


def edges(n):
    return tuple((i, (i + shift) % n) for shift in (0, 1) for i in range(n))


def symmetries(n):
    for k in range(n):
        yield tuple((i + k) % n for i in range(n)), tuple((j + k) % n for j in range(n))
        yield tuple((k - i) % n for i in range(n)), tuple((k + 1 - j) % n for j in range(n))


def full_path(n, i, j):
    return 0, 1 + i, n + 1, n + 2 + j, 2*n + 2


def path_basis(n):
    proper = set()
    for i, j in product(range(n), repeat=2):
        top = full_path(n, i, j)
        proper.update(top[a:b] for a in range(5) for b in range(a + 1, min(a + 5, 6))
                      if b - a < 5)
    return sorted(proper, key=lambda p: (len(p), p)) + [(0, 2*n + 2)]


def align(n, w, w_new, sigma, tau, H, modulus):
    x, y = {0: 1}, {}
    rhs = {(i, j): H * w[i, j] * pow(w_new[sigma[i], tau[j]], -1, modulus) % modulus
           for i, j in edges(n)}
    while len(x) + len(y) < 2*n:
        for (i, j), v in rhs.items():
            if i in x and j not in y:
                y[j] = v * pow(x[i], -1, modulus) % modulus
            if j in y and i not in x:
                x[i] = v * pow(y[j], -1, modulus) % modulus
    if any(x[i]*y[j] % modulus != v for (i, j), v in rhs.items()):
        return None
    return x, y


def transport(n, sigma, tau, H, x, y, q, modulus, basis):
    s, m, t = 0, n + 1, 2*n + 2
    vertex = {s: s, m: m, t: t}
    scale = {}
    for i in range(n):
        left = i + 1
        right = n + 2 + i
        vertex[left] = 1 + sigma[i]
        vertex[right] = n + 2 + tau[i]
        free = q if i == 0 else 1
        scale[s, left] = x[i] * pow(free, -1, modulus) % modulus
        scale[left, m] = free
        scale[m, right] = 1
        scale[right, t] = y[i]
    image = {path: (tuple(vertex[v] for v in path),
                    prod(scale[a, b] for a, b in zip(path, path[1:])) % modulus)
             for path in basis[:-1]}
    image[basis[-1]] = basis[-1], H
    coordinates = {p: i for i, p in enumerate(basis)}
    order = [coordinates[image[p][0]] for p in basis]
    odd = sum(a > b for i, a in enumerate(order) for b in order[i+1:]) % 2
    return (-1)**odd * prod(image[p][1] for p in basis) % modulus, image


def multiply(n, w, p, q):
    if p[-1] != q[0]:
        return None, 0
    word = p + q[1:]
    if len(word) == 5:
        return (0, 2*n + 2), w.get((word[1] - 1, word[3] - n - 2), 0)
    return word, 1


def check_witness(n, w, w_new, basis, image, modulus):
    for p, q in product(basis, repeat=2):
        word, c = multiply(n, w, p, q)
        pp, a = image[p]
        qq, b = image[q]
        new_word, d = multiply(n, w_new, pp, qq)
        if c:
            output, e = image[word]
            assert c*e % modulus == a*b*d % modulus and output == new_word
        else:
            assert d == 0


def determinant_set(n, modulus, w, twisted):
    all_units = [u for u in range(modulus) if gcd(u, modulus) == 1]
    basis = path_basis(n)
    assert len(basis) == 3*n*n + 8*n + 4
    actual = set()
    checked = set()
    for sigma, tau in symmetries(n):
        for H, q in product(all_units, repeat=2):
            xy = align(n, w, twisted, sigma, tau, H, modulus)
            if xy is None:
                continue
            value, image = transport(n, sigma, tau, H, *xy, q, modulus, basis)
            actual.add(value)
            if value not in checked:
                check_witness(n, w, twisted, basis, image, modulus)
                checked.add(value)
    return actual


def main():
    cases = [(2, 3, 1), (3, 3, 1), (3, 3, 2), (3, 5, 4), (3, 7, 2),
             (3, 7, 6), (3, 8, 1), (3, 8, 3), (4, 8, 3), (5, 8, 5)]
    for n, modulus, lam in cases:
        all_units = {u for u in range(modulus) if gcd(u, modulus) == 1}
        squares = {u*u % modulus for u in all_units}
        w = dict.fromkeys(edges(n), 1)
        w[0, 0] = lam
        expected = all_units if n % 2 == 0 else squares
        if n % 2 and lam*lam % modulus == 1:
            expected = expected | {lam*u % modulus for u in expected}
        actual = determinant_set(n, modulus, w, w)
        assert actual == expected
        g = min(all_units - {1})
        twisted = {edge: value * (g if edge[0] == 0 else 1) % modulus
                   for edge, value in w.items()}
        twist_dets = determinant_set(n, modulus, w, twisted)
        assert twist_dets == {a * pow(g, -1, modulus) % modulus for a in expected}
        print(f'C{2*n} over Z/{modulus}, holonomy {lam}: {sorted(actual)} and {sorted(twist_dets)}')


if __name__ == '__main__':
    main()
