from fractions import Fraction
from itertools import combinations, permutations, product
from math import gcd


class CentralPresentation:
    def __init__(self, quotient_orders, central_orders, commutators, powers):
        self.orders = quotient_orders
        self.central_orders = central_orders
        self.pairs = tuple(combinations(range(len(self.orders)), 2))
        self.commutators = dict(zip(self.pairs, commutators))
        self.powers = powers
        self.zero_quotient = (0,) * len(self.orders)
        self.zero_central = (0,) * len(self.central_orders)
        self.identity = (self.zero_quotient, self.zero_central)
        self.quotient = tuple(product(*(range(order) for order in self.orders)))

    def multiply(self, first, second):
        a, central_a = first
        b, central_b = second
        carries = [divmod(x + y, order) for x, y, order in zip(a, b, self.orders)]
        central = []
        for h, modulus in enumerate(self.central_orders):
            value = central_a[h] + central_b[h]
            value += sum(carry * self.powers[i][h] for i, (carry, _) in enumerate(carries))
            value -= sum(a[j] * b[i] * self.commutators[i, j][h] for i, j in self.pairs)
            central.append(value % modulus)
        return tuple(residue for _, residue in carries), tuple(central)

    def power(self, element, exponent):
        result = self.identity
        while exponent:
            if exponent & 1:
                result = self.multiply(result, element)
            element = self.multiply(element, element)
            exponent //= 2
        return result

    def power_record(self, m, quotient, central=None):
        central = self.zero_central if central is None else central
        quotient_power, power = self.power((quotient, central), m)
        assert quotient_power == self.zero_quotient
        return tuple(x % gcd(m, order) for x, order in zip(power, self.central_orders))

    def beta(self, a, b):
        return tuple(sum((a[i] * b[j] - a[j] * b[i]) * self.commutators[i, j][h]
                         for i, j in self.pairs) % order
                     for h, order in enumerate(self.central_orders))

    def check_powers(self):
        evaluated = 0
        for m in set(self.orders):
            factors = [gcd(m, n) for n in self.orders]
            moduli = [gcd(m, n) for n in self.central_orders]
            masks = [n // d for n, d in zip(self.orders, factors)]
            torsion = tuple(a for a in self.quotient if all(m * x % n == 0 for x, n in zip(a, self.orders)))
            lifted_values = {a: self.power_record(m, a) for a in torsion}
            choices = tuple(product(*(range(order) for order in self.central_orders)))
            for a in torsion:
                for central in choices:
                    assert self.power_record(m, a, central) == lifted_values[a]
                coordinates = [x // d for x, d in zip(a, masks)]
                coefficients = []
                for h, modulus in enumerate(moduli):
                    value = sum((m // factors[i]) * self.powers[i][h] * x
                                for i, x in enumerate(coordinates) if factors[i] > 1)
                    value -= sum((m * (m - 1) // 2) * self.commutators[i, j][h]
                                 * masks[i] * masks[j] * coordinates[i] * coordinates[j]
                                 for i, j in self.pairs)
                    coefficients.append(value % modulus)
                assert tuple(coefficients) == lifted_values[a]
                for b in torsion:
                    summed = tuple((x + y) % n for x, y, n in zip(a, b, self.orders))
                    expected = tuple((x + y - (m * (m - 1) // 2) * z) % mod
                                     for x, y, z, mod in zip(lifted_values[a], lifted_values[b],
                                                             self.beta(a, b), moduli))
                    assert lifted_values[summed] == expected
                    evaluated += 1
        return evaluated


def eta(vector):
    x, y = vector
    return x, y, x * (x - 1) // 2, y * (y - 1) // 2, x * y


def polar(a, b):
    x, y = a
    z, w = b
    return 0, 0, x * z, y * w, x * w + y * z


def marking(coordinates):
    a, b, d, e, c = coordinates
    return a, b, a + 2 * d, b + 2 * e, c, c


def determinant(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    answer = 1
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i]), None)
        if pivot is None:
            return 0
        answer *= -1 if pivot != i else 1
        rows[i], rows[pivot] = rows[pivot], rows[i]
        entry = rows[i][i]
        answer *= entry
        for j in range(i + 1, len(rows)):
            scale = rows[j][i] / entry
            rows[j] = [x - scale * y for x, y in zip(rows[j], rows[i])]
    assert answer.denominator == 1
    return answer.numerator


def check_marking_and_action():
    kernel_visits = action_visits = 0
    for modulus in range(2, 9):
        for coordinates in product(range(modulus), repeat=5):
            a, b, d, e, c = coordinates
            vanishes = all(value % modulus == 0 for value in marking(coordinates))
            assert vanishes == (a == b == c == 0 and 2 * d % modulus == 2 * e % modulus == 0)
            kernel_visits += 1
        found = 0
        for u, v, w, z in product(range(modulus), repeat=4):
            if gcd(u * z - v * w, modulus) != 1:
                continue
            first = (u, w)
            second = (v, z)
            columns = [eta(first), eta(second), polar(first, first), polar(second, second), polar(first, second)]
            rows = tuple(zip(*columns))
            assert gcd(determinant(rows), modulus) == 1
            for x, y in product(range(-2, 3), repeat=2):
                source = eta((x, y))
                target = (u * x + v * y, w * x + z * y)
                image = tuple(sum(a * b for a, b in zip(row, source)) for row in rows)
                assert image == eta(target)
                assert marking(image) == (*target, target[0] ** 2, target[1] ** 2,
                                          target[0] * target[1], target[1] * target[0])
                action_visits += 1
            found += 1
            if found == 10:
                break
    return kernel_visits, action_visits


def check_order_eight(dihedral, quaternion):
    nonzero = tuple(a for a in dihedral.quotient if a != (0, 0))
    pairs = tuple(permutations(nonzero, 2))

    def compatible(source, target):
        success = 0
        for a, b in pairs:
            def image(x):
                return tuple((x[0] * u + x[1] * v) % 2 for u, v in zip(a, b))

            matches = (target.beta(a, b) == source.beta((1, 0), (0, 1))
                       and all(source.power_record(2, x) == target.power_record(2, image(x))
                               for x in source.quotient))
            success += matches
        return success

    assert compatible(dihedral, quaternion) == 0
    assert compatible(dihedral, dihedral) * 4 == 8
    assert compatible(quaternion, quaternion) * 4 == 24


if __name__ == '__main__':
    dihedral = CentralPresentation((2, 2), (2,), ((1,),), ((1,), (0,)))
    quaternion = CentralPresentation((2, 2), (2,), ((1,),), ((1,), (1,)))
    ring_4 = CentralPresentation((2, 4), (2,), ((1,),), ((1,), (1,)))
    ring_9 = CentralPresentation((3, 9), (3,), ((1,),), ((1,), (2,)))
    ring_12 = CentralPresentation((4, 6, 6), (2, 3), ((1, 0), (0, 0), (1, 1)),
                                  ((1, 1), (0, 2), (1, 0)))
    comparisons = sum(g.check_powers() for g in (dihedral, quaternion, ring_4, ring_9, ring_12))
    kernel_cases, action_cases = check_marking_and_action()
    check_order_eight(dihedral, quaternion)
    print(f'PASS: {comparisons} power comparisons, {kernel_cases} kernel cases, '
          f'{action_cases} lifted quadratic action cases, and exact order-eight controls')
