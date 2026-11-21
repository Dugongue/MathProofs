"""Exact F_9 controls for the four-arm coefficient-field tag."""

from itertools import product


# a + b*i is encoded as a + 3*b, with i*i = -1.
FIELD = range(9)
THETA = 3
ARM_SIZES = (0, 2, 4, 6)


def add(a, b):
    return (a % 3 + b % 3) % 3 + 3 * ((a // 3 + b // 3) % 3)


def neg(a):
    return (-a % 3) + 3 * ((-(a // 3)) % 3)


def mul(a, b):
    x, y = a % 3, a // 3
    z, w = b % 3, b // 3
    return (x * z - y * w) % 3 + 3 * ((x * w + y * z) % 3)


def power(a, n):
    out = 1
    for _ in range(n):
        out = mul(out, a)
    return out


def determinant(v, w):
    return add(mul(v[0], w[1]), neg(mul(v[1], w[0])))


def dimension(vectors, size):
    echelon = {}
    for row in vectors:
        row = list(row)
        for i in range(size):
            if not row[i]:
                continue
            if i in echelon:
                scale = row[i]
                row = [add(x, neg(mul(scale, y))) for x, y in zip(row, echelon[i])]
                continue
            echelon[i] = [mul(x, power(row[i], 7)) for x in row]
            break
    return len(echelon)


def frame_control():
    top = ((1, 0), (0, 1), (1, 1), (1, THETA))
    for use_frobenius in (False, True):
        source = (
            tuple(tuple(power(x, 3) for x in v) for v in top) if use_frobenius else top
        )
        matches = 0
        for a, b, c, d in product(FIELD, repeat=4):
            if determinant((a, b), (c, d)) == 0:
                continue
            images = (
                (add(mul(a, x), mul(b, y)), add(mul(c, x), mul(d, y))) for x, y in source
            )
            matches += all(determinant(v, w) == 0 for v, w in zip(images, top))
        assert matches == (0 if use_frobenius else 8)

    for coeff in product(FIELD, repeat=4):
        contraction_image = [v for a, v in zip(coeff, top) if a]
        rank = dimension(contraction_image, 2)
        assert rank == min(2, len(contraction_image))

    count = 0
    for values in product(range(1, 9), repeat=4):
        powers = tuple(power(a, 4) for a in values)
        if len(set(powers)) != 1:
            continue
        b = powers[0]
        value = power(b, 2)
        for a, r in zip(values, ARM_SIZES):
            value = mul(value, power(a, 6 + r))
        assert power(value, 4) == 1
        count += 1
    assert count == 8 * 4**3
    assert power(add(1, THETA), 4) == 2
    print(f"6,561 contraction supports and {count} common-fourth-power norm choices checked")
    print("ordered top lines admit 8 linear maps and no conjugate-semilinear map")


class Tag:
    """Based tag algebra. Elements are sparse dictionaries of coefficients."""

    def __init__(self):
        self.unit = ("one",)
        self.s = ("s",)
        self.t = ("t",)
        self.basis = [self.unit, self.s, self.t]
        self.b1 = []
        self.b2 = []
        self.tops = ({self.s: 1}, {self.t: 1}, {self.s: 1, self.t: 1}, {self.s: 1, self.t: THETA})
        for i, r in enumerate(ARM_SIZES):
            self.basis.extend(("u", i, j) for j in (1, 2, 3))
            self.basis.extend(("w", i, j) for j in range(r))
            self.basis.extend(("E", i, j) for j in range(r))
            self.b1.extend([("u", i, 1), *(("w", i, j) for j in range(r))])
            self.b2.extend([("u", i, 2), *(("E", i, j) for j in range(r))])

    def basis_product(self, a, b):
        if a == self.unit:
            return {b: 1}
        if b == self.unit:
            return {a: 1}
        if a[0] == b[0] == "u" and a[1] == b[1]:
            degree = a[2] + b[2]
            if degree < 4:
                return {("u", a[1], degree): 1}
            if degree == 4:
                return self.tops[a[1]]
        if a[0] == "w":
            a, b = b, a
        if a[0] == "u" and b[0] == "w" and a[1] == b[1] and a[2] == 1:
            return {("E", b[1], b[2]): 1}
        return {}

    def element_product(self, a, b):
        out = {}
        for i, x in a.items():
            for j, y in b.items():
                for k, c in self.basis_product(i, j).items():
                    out[k] = add(out.get(k, 0), mul(mul(x, y), c))
        return {key: value for key, value in out.items() if value}


def tag_control():
    tag = Tag()
    assert len(tag.basis) == 39
    for a, b, c in product(tag.basis, repeat=3):
        left = tag.element_product(tag.basis_product(a, b), {c: 1})
        right = tag.element_product({a: 1}, tag.basis_product(b, c))
        assert left == right

    for i, r in enumerate(ARM_SIZES):
        axis = ("u", i, 1)
        markers = [v for v in tag.b1 if v[0] == "w"]
        lifts = [{axis: 1}]
        lifts.extend({axis: 1, v: a} for a, v in product(range(1, 9), markers))
        ranks = []
        for lift in lifts:
            rows = []
            for target in tag.b1:
                image = tag.element_product(lift, {target: 1})
                rows.append([image.get(component, 0) for component in tag.b2])
            ranks.append(dimension(rows, len(tag.b2)))
        assert min(ranks) == r + 1
    print("59,319 basis associativity checks and the four degree-two rank labels verified")


if __name__ == "__main__":
    frame_control()
    tag_control()

