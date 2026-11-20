from functools import lru_cache
from itertools import product


class Field:
    def __init__(self, order):
        assert order in (2, 3, 4)
        self.order = order

    def add(self, a, b):
        return a ^ b if self.order == 4 else (a + b) % self.order

    def neg(self, a):
        return a if self.order == 4 else (-a) % self.order

    def mul(self, a, b):
        if self.order != 4:
            return (a * b) % self.order
        # F4 is presented using z^2 + z + 1.
        answer = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
        return answer ^ 7 if answer & 4 else answer

    def power(self, a, degree):
        answer = 1
        for _ in range(degree):
            answer = self.mul(answer, a)
        return answer

    def sum(self, entries):
        answer = 0
        for value in entries:
            answer = self.add(answer, value)
        return answer

    def polynomial(self, values):
        while values and values[-1] == 0:
            values.pop()
        return tuple(values)

    def polynomial_sub(self, a, b):
        return self.polynomial([self.add(a[i] if i < len(a) else 0,
                                         self.neg(b[i]) if i < len(b) else 0)
                                for i in range(max(len(a), len(b)))])

    def polynomial_mul(self, a, b):
        result = [0] * (len(a) + len(b))
        for i, u in enumerate(a):
            for j, v in enumerate(b):
                result[i + j] = self.add(result[i + j], self.mul(u, v))
        return self.polynomial(result)

    def polynomial_exact_div(self, numerator, denominator):
        assert denominator
        result = [0] * max(0, len(numerator) - len(denominator) + 1)
        inverse = self.power(denominator[-1], self.order - 2)
        while len(numerator) >= len(denominator):
            power = len(numerator) - len(denominator)
            value = self.mul(numerator[-1], inverse)
            result[power] = value
            numerator = self.polynomial_sub(numerator, (0,) * power + tuple(
                self.mul(value, coefficient) for coefficient in denominator))
        assert not numerator
        return self.polynomial(result)


def characteristic_polynomial(field, matrix):
    # Bareiss on tI − M. All successive leading principal determinants are monic.
    size = len(matrix)
    matrix = [[field.polynomial([field.neg(value), int(i == j)])
               for j, value in enumerate(row)] for i, row in enumerate(matrix)]
    previous = (1,)
    for k in range(size - 1):
        current = matrix[k][k]
        assert current[-1] == 1
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                determinant = field.polynomial_sub(field.polynomial_mul(current, matrix[i][j]),
                    field.polynomial_mul(matrix[i][k], matrix[k][j]))
                matrix[i][j] = field.polynomial_exact_div(determinant, previous)
        previous = current
    return matrix[-1][-1]


def algebra_norm(field, q, matrix, x):
    n = len(x)
    basis = list(product(range(q), repeat=n))
    row_index = {monomial: i for i, monomial in enumerate(basis)}

    @lru_cache(None)
    def normal_form(monomial):
        for i, exponent in enumerate(monomial):
            if exponent < q:
                continue
            result = {}
            reduced = list(monomial)
            reduced[i] -= q
            for j in range(n):
                if not matrix[j][i]:
                    continue
                reduced[j] += 1
                for mon, value in normal_form(tuple(reduced)).items():
                    result[mon] = field.add(result.get(mon, 0), field.mul(matrix[j][i], value))
                reduced[j] -= 1
            return result
        return {monomial: 1}

    multiplication = [[0] * len(basis) for _ in basis]
    for col, monomial in enumerate(basis):
        for i, value in enumerate(x):
            if not value:
                continue
            times_y = list(monomial)
            times_y[i] += 1
            for mon, coefficient in normal_form(tuple(times_y)).items():
                row = row_index[mon]
                multiplication[row][col] = field.add(multiplication[row][col],
                                                      field.mul(value, coefficient))
    return characteristic_polynomial(field, multiplication)


def direct_product(field, q, x):
    candidates = [a for a in range(field.order) if field.power(a, q) == a]
    assert len(candidates) == q
    result = (1,)
    for y in product(candidates, repeat=len(x)):
        value = field.sum(field.mul(v, w) for v, w in zip(y, x))
        result = field.polynomial_mul(result, (field.neg(value), 1))
    return result


def multiplication(field, A, B):
    return tuple(tuple(field.sum(field.mul(v, w) for v, w in zip(row, column))
                       for column in zip(*B)) for row in A)


def inverse2(field, g):
    (a, b), (c, d) = g
    det = field.add(field.mul(a, d), field.neg(field.mul(b, c)))
    inverse = field.power(det, field.order - 2)
    assert field.mul(inverse, det) == 1
    return tuple(tuple(field.mul(inverse, entry) for entry in row)
                 for row in ((d, field.neg(b)), (field.neg(c), a)))


def run():
    guard_count, covariance_count = 0, 0
    for order, q, n in ((2, 2, 3), (3, 3, 2), (4, 2, 2), (4, 4, 2)):
        field = Field(order)
        I = tuple(tuple(int(i == j) for j in range(n)) for i in range(n))
        for x in product(range(order), repeat=n):
            assert algebra_norm(field, q, I, x) == direct_product(field, q, x)
            guard_count += 1
        e1 = (1,) + (0,) * (n - 1)
        assert direct_product(field, q, e1)[q ** (n - 1)] == field.neg(1)
        assert direct_product(field, q, (0,) * n)[q ** (n - 1)] == 0

    field = Field(4)
    for shift in (0, 1):
        q = 2 ** (shift + 1)
        for index, (a, b, c, d) in enumerate(product(range(4), repeat=4)):
            if index % 5:
                continue
            A = ((a, b), (c, d))
            g = ((1, (index % 3) + 1), (0, 2 + index % 2))
            g_inverse_frobenius = tuple(tuple(field.power(value, q) for value in row)
                                        for row in inverse2(field, g))
            A_after = multiplication(field, multiplication(field, g, A), g_inverse_frobenius)
            x = ((index % 3) + 1, (index // 3) % 4)
            x_after = tuple(row[0] for row in multiplication(field, g, tuple((v,) for v in x)))
            assert algebra_norm(field, q, A, x) == algebra_norm(field, q, A_after, x_after)
            covariance_count += 1
    print(f'PASS: {guard_count} fixed-slice Dickson products and {covariance_count} exact '
          'change-of-coordinates checks, including singular link matrices')


if __name__ == '__main__':
    run()
