"""Small exact checks of literal determinant profiles on multiplication tensors."""
from itertools import product


class Field:
    def __init__(self, size):
        self.size = size

    def add(self, a, b):
        return a ^ b if self.size == 4 else (a + b) % self.size

    def neg(self, a):
        return a if self.size == 4 else (-a) % self.size

    def mul(self, a, b):
        if self.size != 4:
            return a * b % self.size
        raw = (a if b & 1 else 0) ^ (a << 1 if b & 2 else 0)
        return raw ^ 7 if raw & 4 else raw

    def pow(self, a, power):
        out = 1
        for _ in range(power):
            out = self.mul(out, a)
        return out

    def inv(self, a):
        assert a
        return self.pow(a, self.size - 2)

    def det(self, rows):
        rows = [list(row) for row in rows]
        out = 1
        for j in range(len(rows)):
            pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
            if pivot is None:
                return 0
            if pivot != j:
                rows[j], rows[pivot] = rows[pivot], rows[j]
                out = self.neg(out)
            out = self.mul(out, rows[j][j])
            inverse = self.inv(rows[j][j])
            for i in range(j + 1, len(rows)):
                ratio = self.neg(self.mul(rows[i][j], inverse))
                for k in range(j, len(rows)):
                    rows[i][k] = self.add(rows[i][k], self.mul(ratio, rows[j][k]))
        return out


def ring_product(field, x, y):
    result = [0] * len(x)
    for i, a in enumerate(x):
        for j, b in enumerate(y[:len(x) - i]):
            result[i + j] = field.add(result[i + j], field.mul(a, b))
    return result


def gram(field, weights):
    size = len(weights)
    return field.det([[weights[i + j] if i + j < size else 0
                       for j in range(size)] for i in range(size)])


def check(field, size):
    nonzero = list(range(1, field.size))
    units = set()
    for coefficients in product(range(field.size), repeat=size):
        if coefficients[0] == 0:
            continue
        matrix = [[coefficients[i - j] if i >= j else 0 for j in range(size)]
                  for i in range(size)]
        units.add(field.det(matrix))
    assert units == {field.pow(a, size) for a in nonzero}

    weights_a = [1] * size
    weights_b = [0] * (size - 1) + [1]
    determinants = set()
    substituted = 0
    for coefficients in product(range(field.size), repeat=size - 1):
        if coefficients[0] == 0:
            continue
        x = [0, *coefficients]
        columns = [[1] + [0] * (size - 1)]
        for _ in range(size - 1):
            columns.append(ring_product(field, columns[-1], x))
        determinant = field.det(list(zip(*columns)))
        alpha = columns[-1][-1]
        paired = field.mul(field.pow(determinant, 2), gram(field, weights_b))
        assert paired == field.mul(gram(field, weights_a), field.pow(alpha, size))
        if field.size == 4:
            for expected in nonzero:
                assert (determinant == expected) == (
                    field.pow(expected, 2) == field.pow(alpha, size))
        half = (size + 1) // 2
        r = size - half
        middle = columns[r][r] if size % 2 else 1
        assert determinant == field.mul(field.pow(alpha, r), middle)
        determinants.add(determinant)
        substituted += 1

    profiles = {(field.mul(x, h), field.mul(y, h), field.mul(field.mul(x, y), h))
                for x, y, h in product(units, units, determinants)}
    for first, second in product(nonzero, repeat=2):
        predicted = (field.mul(first, second) in determinants and field.inv(first) in units
                     and field.inv(second) in units)
        assert predicted == ((first, second, 1) in profiles)
    return substituted, len(nonzero) ** 2


if __name__ == "__main__":
    counts = [check(Field(q), n) for q, n in product((2, 3, 4, 5), (2, 3, 4, 5))]
    print("Truncated local algebra tests:", len(counts))
    print("Automorphism substitutions:", sum(a for a, _ in counts))
    print("Normalized coordinate determinant targets:", sum(b for _, b in counts))
