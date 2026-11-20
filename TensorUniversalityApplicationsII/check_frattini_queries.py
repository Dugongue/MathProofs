from itertools import product


class CentralTable:
    """One-dimensional central coordinate, with independent generator records."""

    def __init__(self, p, powers, commutator):
        self.p = p
        self.powers = tuple(powers)
        self.commutator = commutator
        self.n = len(self.powers)
        self.elements = tuple(product(range(p), repeat=self.n + 1))
        self.index = dict(zip(self.elements, range(len(self.elements))))
        self.rows = [[self.index[self.multiply(a, b)] for b in self.elements] for a in self.elements]
        self.central = self.index[(0,) * self.n + (1,)]

    def multiply(self, a, b):
        residues = tuple((a[i] + b[i]) % self.p for i in range(self.n))
        carries = sum((a[i] + b[i]) // self.p * self.powers[i] for i in range(self.n))
        crossing = a[1] * b[0] * self.commutator if self.n == 2 else 0
        return residues + ((a[-1] + b[-1] + carries + crossing) % self.p,)

    def power(self, element, exponent):
        result = 0
        for _ in range(exponent):
            result = self.rows[result][element]
        return result

    def full_power(self, v):
        value = sum(a * q for a, q in zip(v, self.powers))
        if self.p == 2 and self.n == 2:
            value += self.commutator * v[0] * v[1]
        return value % self.p

    def commutes(self, x, y):
        return self.rows[x][y] == self.rows[y][x]

    def check_group(self):
        order = len(self.elements)
        identity = list(range(order))
        assert self.rows[0] == identity
        assert [row[0] for row in self.rows] == identity
        for row in self.rows:
            assert sorted(row) == identity
        for a, b, c in product(range(order), repeat=3):
            assert self.rows[self.rows[a][b]][c] == self.rows[a][self.rows[b][c]]
        for index, element in enumerate(self.elements):
            expected = self.index[(0,) * self.n + (self.full_power(element[:-1]),)]
            assert self.power(index, self.p) == expected
            assert self.commutes(index, self.central)
        return order ** 3


def independent_columns(columns, p):
    if len(columns) == 1:
        return columns[0][0] != 0
    (a, c), (b, d) = columns
    return (a * d - b * c) % p != 0


def transfer_count(source, target):
    p, n = source.p, source.n
    predicted = 0
    vectors = tuple(product(range(p), repeat=n))
    for cols in product(vectors, repeat=n):
        if not independent_columns(cols, p):
            continue
        for h in range(1, p):
            if not all(target.full_power(col) == h * s % p for col, s in zip(cols, source.powers)):
                continue
            if n == 2:
                (a, c), (b, d) = cols
                if (a * d - b * c) * target.commutator % p != h * source.commutator % p:
                    continue
            predicted += p ** n

    enumerated = 0
    order = len(source.elements)
    target_rows = target.rows
    for images in product(range(order), repeat=n):
        image_words = [tuple(target.power(i, j) for j in range(p)) for i in images]
        for central_scalar in range(1, p):
            central_image = [target.power(target.central, central_scalar * j) for j in range(p)]
            mapped = []
            for word in source.elements:
                image = 0
                for i, a in enumerate(word[:-1]):
                    image = target_rows[image][image_words[i][a]]
                mapped.append(target_rows[image][central_image[word[-1]]])
            if len(set(mapped)) != order:
                continue
            if all(mapped[source.rows[x][y]] == target_rows[mapped[x]][mapped[y]]
                   for x, y in product(range(order), repeat=2)):
                enumerated += 1
    assert predicted == enumerated, (p, source.powers, target.powers, predicted, enumerated)
    return enumerated


def marker_checks():
    # Work in the homogeneous carrier with basis e1,e2,e3,z over F3.
    p = 3
    tests = 0
    for data in product(range(p), repeat=9):
        columns = [data[i:i + 3] for i in (0, 3, 6)]
        a, b, c = columns
        determinant = (a[0] * (b[1] * c[2] - b[2] * c[1])
                       - a[1] * (b[0] * c[2] - b[2] * c[0])
                       + a[2] * (b[0] * c[1] - b[1] * c[0])) % p
        if not determinant:
            continue
        wedge = [(a[i] * b[j] - a[j] * b[i]) % p for i, j in ((0, 1), (0, 2), (1, 2))]
        for anchor in (1, 2):
            action = wedge + [(anchor * x) % p for x in c]
            inverse = pow(anchor, -1, p)
            sa, sb, sc = [tuple(inverse * x % p for x in column) for column in columns]
            corrected = [(sa[i] * sb[j] - sa[j] * sb[i]) % p for i, j in ((0, 1), (0, 2), (1, 2))]
            corrected += list(sc)
            assert action == [anchor ** 2 * x % p for x in corrected]
            tests += 1

    # Adding the single hyperplane slot gives a distinct incidence signal,
    # with no change on lines and planes as all those have dimension below three.
    e0, e1, e2, z = [tuple(int(i == j) for j in range(4)) for i in range(4)]
    total = tuple((a + b + c) % p for a, b, c in zip(e0, e1, z))
    old = [(z,), (e0,), (e0,), (e1,), (e1,), (e1,)] + [(total,)] * 4
    new = old + [(e0, e1, e2)]
    recovered = set()
    for functional in product(range(p), repeat=4):
        if not any(functional):
            continue

        def contained(basis):
            return all(sum(a * b for a, b in zip(functional, v)) % p == 0 for v in basis)

        delta = sum(contained(basis) for basis in new) - sum(contained(basis) for basis in old)
        if delta:
            inverse = pow(next(x for x in functional if x), -1, p)
            recovered.add(tuple(x * inverse % p for x in functional))
    assert recovered == {z}
    return tests


if __name__ == '__main__':
    binary = [CentralTable(2, (a, b), c) for a, b, c in product(range(2), repeat=3) if a or b or c]
    ternary = [CentralTable(3, (1,), 0), CentralTable(3, (0, 0), 1),
               CentralTable(3, (1, 0), 1), CentralTable(3, (1, 0), 0)]
    laws = sum(g.check_group() for g in binary + ternary)
    pairs = list(product(binary, repeat=2))
    pairs += list(product(ternary[1:], repeat=2)) + [(ternary[0], ternary[0])]
    for source, target in pairs:
        transfer_count(source, target)
    pure_square = CentralTable(2, (1, 0), 0)
    assert pure_square.full_power((1, 0)) == 1
    assert all(pure_square.commutes(a, b) for a, b in product(range(8), repeat=2))
    dihedral, quaternion = CentralTable(2, (0, 0), 1), CentralTable(2, (1, 1), 1)
    assert dihedral.commutator == quaternion.commutator
    assert transfer_count(dihedral, quaternion) == 0
    markers = marker_checks()
    print(f'PASS: {laws} associativity triples, {len(pairs)} exact transporter counts, '
          f'{markers} anchor normalizations; pure-square and hyperplane controls passed')
