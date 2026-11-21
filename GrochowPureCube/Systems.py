"""Exact finite controls over F_3 for ordered cubic system transporters."""

from collections import Counter
from itertools import combinations_with_replacement, product


Q = 3


def matrices(n):
    """Enumerate GL(n,3), storing row vectors."""
    vectors = list(product(range(Q), repeat=n))

    def extend(rows, span):
        if len(rows) == n:
            yield rows
            return
        for row in vectors:
            if row in span:
                continue
            enlarged = {
                tuple((a + t * b) % Q for a, b in zip(vector, row))
                for vector in span
                for t in range(Q)
            }
            yield from extend(rows + (row,), enlarged)

    yield from extend((), {(0,) * n})


def multiply(left, right):
    return tuple(
        tuple(sum(a * b for a, b in zip(row, column)) % Q for column in zip(*right))
        for row in left
    )


def unit(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


class Cubics:
    def __init__(self, n):
        self.n = n
        self.monomials = list(combinations_with_replacement(range(n), 3))
        self.indices = {monomial: i for i, monomial in enumerate(self.monomials)}
        self.pure = tuple(len(set(monomial)) == 1 for monomial in self.monomials)

    def polynomial(self, terms):
        coeff = [0] * len(self.monomials)
        for monomial, value in terms.items():
            coeff[self.indices[monomial]] = value
        return tuple(coeff)

    def substitution(self, matrix):
        columns = []
        for i, j, k in self.monomials:
            column = [0] * len(self.monomials)
            for a, b, c in product(range(self.n), repeat=3):
                index = self.indices[tuple(sorted((a, b, c)))]
                column[index] += matrix[i][a] * matrix[j][b] * matrix[k][c]
            columns.append(tuple(value % Q for value in column))
        return tuple(zip(*columns))

    def apply(self, substitution, coeff):
        return tuple(sum(a * b for a, b in zip(row, coeff)) % Q for row in substitution)

    def polar(self, coeff):
        return tuple(value for value, pure in zip(coeff, self.pure) if not pure)


def binary_control():
    cubics = Cubics(2)
    group = tuple(matrices(2))
    all_cubics = tuple(product(range(Q), repeat=4))
    substitutions = {matrix: cubics.substitution(matrix) for matrix in group}
    images = {
        matrix: {f: cubics.apply(substitutions[matrix], f) for f in all_cubics}
        for matrix in group
    }
    inverse = {
        a: next(b for b in group if multiply(a, b) == unit(2)) for a in group
    }
    f = (1, 1, 2, 2)
    g = (2, 2, 1, 0)
    source = (f, g)
    direct = Counter((images[a][f], images[a][g]) for a in group)
    individual_targets = tuple(
        {images[a][component] for a in group} for component in source
    )
    proper_simultaneous_negative = 0
    for target in product(all_cubics, repeat=2):
        polars = tuple(map(cubics.polar, target))
        # Pushforward on forms uses the substitution by A^{-1}.
        def act(a, form):
            return images[inverse[a]][form]

        polarization_transporter = [
            a for a in group if tuple(cubics.polar(act(a, u)) for u in source) == polars
        ]
        expected = direct[target]
        if not polarization_transporter:
            assert expected == 0
            continue

        h_group = [
            a for a in group if tuple(cubics.polar(act(a, u)) for u in target) == polars
        ]
        representative = polarization_transporter[0]
        order = len(h_group)
        for u, v in zip(source, target):
            moved = act(representative, u)
            orbit = {act(h, moved): h for h in h_group}
            assert len(orbit) <= Q**2
            if v not in orbit:
                order = 0
                break
            representative = multiply(orbit[v], representative)
            h_group = [h for h in h_group if act(h, v) == v]
            order, remainder = divmod(order, len(orbit))
            assert remainder == 0
            assert order == len(h_group)
        assert order == expected, (target, order, expected)
        if order:
            assert tuple(act(representative, u) for u in source) == target
        if not order and all(t in orbit for t, orbit in zip(target, individual_targets)):
            proper_simultaneous_negative += 1

    assert proper_simultaneous_negative > 0
    print(
        f"{len(all_cubics)**2} ordered target pairs checked; "
        f"{proper_simultaneous_negative} negative pairs individually reachable"
    )


def radical_control():
    cubics = Cubics(3)
    base = {(0, 0, 1): 1}
    f = cubics.polynomial(base)
    f_plus = cubics.polynomial({**base, (2, 2, 2): 1})
    f_twice = cubics.polynomial({**base, (2, 2, 2): 2})
    f_shift = cubics.polynomial({**base, (0, 0, 0): 1, (2, 2, 2): 2})
    x3 = cubics.polynomial({(0, 0, 0): 1})
    y3 = cubics.polynomial({(1, 1, 1): 1})
    systems = ((f, f), (f_plus, f_twice), (f_plus, f_shift), (x3, y3))
    counts = [0] * len(systems)
    unequal_radical_image = 0
    for matrix in matrices(3):
        substitution = cubics.substitution(matrix)
        for i, system in enumerate(systems):
            images = tuple(cubics.apply(substitution, g) for g in system)
            counts[i] += images == system
            if i == 1:
                unequal_radical_image += images == (f_plus, f_plus)

    binary = Cubics(2)
    b = binary.polynomial({(0, 0, 1): 1})
    b_shift = binary.polynomial({(0, 0, 1): 1, (0, 0, 0): 1})
    quotient_orders = [
        sum(binary.apply(binary.substitution(a), s) == s for a in matrices(2))
        for s in (b, b, b_shift)
    ]
    # c=2: (r,t)=(1,0),(1,1),(1,1). c=0: (r,t)=(3,2).
    assert counts == [18 * quotient_orders[0], *quotient_orders[1:], 18]
    assert unequal_radical_image == 0
    print(f"four exhaustive GL(3,3) stabilizer counts {counts}; unequal images rejected")


if __name__ == "__main__":
    binary_control()
    radical_control()

