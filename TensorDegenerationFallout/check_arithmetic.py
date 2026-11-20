"""Small finite controls for field guards and the auxiliary singularity."""

from itertools import permutations, product


class QuadraticField:
    """Use x²+x+1 over F2 and x²+1 over F3."""

    def __init__(self, prime):
        assert prime in (2, 3)
        self.p = prime
        self.elements = range(prime * prime)

    def add(self, a, b):
        p = self.p
        return (a % p + b % p) % p + p * (a // p + b // p) % (p*p)

    def neg(self, a):
        p = self.p
        return (-a % p) + p * (-(a // p) % p)

    def mul(self, a, b):
        p = self.p
        a0, a1 = a % p, a // p
        b0, b1 = b % p, b // p
        quadratic = a1*b1
        constant = (a0*b0 - quadratic) % p
        linear = (a0*b1 + a1*b0 - (quadratic if p == 2 else 0)) % p
        return constant + p*linear

    def power(self, a, exponent):
        result = 1
        for _ in range(exponent):
            result = self.mul(result, a)
        return result

    def add_all(self, values):
        result = 0
        for value in values:
            result = self.add(result, value)
        return result


def det2(entries, field):
    a, b, c, d = entries
    return field.add(field.mul(a, d), field.neg(field.mul(b, c)))


def apply2(entries, vector, field):
    a, b, c, d = entries
    x, y = vector
    return (field.add(field.mul(a, x), field.mul(b, y)),
            field.add(field.mul(c, x), field.mul(d, y)))


def multiply_poly(first, second, field):
    result = [0] * (len(first) + len(second) - 1)
    for i, a in enumerate(first):
        for j, b in enumerate(second):
            result[i+j] = field.add(result[i+j], field.mul(a, b))
    return result


def power_poly(linear, exponent, field):
    result = [1]
    for _ in range(exponent):
        result = multiply_poly(result, linear, field)
    return tuple(result)


def guard_control(field):
    p = field.p
    matrices = [entries for entries in product(field.elements, repeat=4)
                if det2(entries, field)]
    prime_survivors = []
    for matrix in matrices:
        a, b, c, d = matrix
        image_first = power_poly((a, c), p, field)
        image_second = power_poly((b, d), p, field)
        linked = (image_first == (a,) + (0,)*(p-1) + (c,)
                  and image_second == (b,) + (0,)*(p-1) + (d,))
        assert linked == all(entry < p for entry in matrix)
        if linked:
            prime_survivors.append(matrix)
        next_matrix = tuple(field.power(entry, p) for entry in matrix)
        a_next, b_next, c_next, d_next = next_matrix
        assert image_first == (a_next,) + (0,)*(p-1) + (c_next,)
        assert image_second == (b_next,) + (0,)*(p-1) + (d_next,)
        assert tuple(field.power(entry, p) for entry in next_matrix) == matrix
    assert len(prime_survivors) == (p*p-1)*(p*p-p)
    return len(matrices), prime_survivors


def scalar_restriction_control(field, prime_matrices, source, target):
    p = field.p
    def digits(value):
        return value % p, value // p

    def from_digits(vector):
        return vector[0] + p*vector[1]

    def acts(matrix, value):
        return from_digits(apply2(matrix, digits(value), field))

    theta = p
    commutants = [
        matrix for matrix in prime_matrices
        if all(acts(matrix, field.mul(theta, x)) == field.mul(theta, acts(matrix, x))
               for x in (1, theta))
    ]
    assert set(acts(matrix, 1) for matrix in commutants) == set(field.elements) - {0}
    assert len(commutants) == p*p - 1
    observed = sum(
        all(
            acts(output, field.mul(source, field.mul(x, y)))
            == field.mul(target, field.mul(acts(first, x), acts(second, y)))
            for x, y in product((1, theta), repeat=2)
        )
        for first, second, output in product(commutants, repeat=3)
    )
    directly = sum(
        field.mul(r, source) == field.mul(target, field.mul(g, h))
        for g, h, r in product(range(1, p*p), repeat=3)
    )
    assert observed == directly
    return observed


def cone_control(field):
    ranks_at_most_one = {matrix for matrix in product(field.elements, repeat=4)
                         if det2(matrix, field) == 0}
    rank_one_orbit = {
        tuple(field.mul(x, y) for x in left for y in right)
        for left, right in product(
            tuple(v for v in product(field.elements, repeat=2) if any(v)), repeat=2
        )
    }
    assert ranks_at_most_one - rank_one_orbit == {(0, 0, 0, 0)}
    zero_jacobian = {
        (a, b, c, d) for a, b, c, d in ranks_at_most_one
        if (d, field.neg(c), field.neg(b), a) == (0, 0, 0, 0)
    }
    assert zero_jacobian == {(0, 0, 0, 0)}
    return len(rank_one_orbit)


def coordinate_algebra_control():
    # The basis images of an invertible algebra map are independent,
    # pairwise orthogonal, nonzero idempotents.
    axes = set(range(1, 8))
    basis_images = {
        elements for elements in product(axes, repeat=3)
        if all(not elements[i] & elements[j] for i in range(3) for j in range(i+1, 3))
    }
    assert basis_images == set(permutations((1, 2, 4)))
    return len(basis_images)


def main():
    for prime in (2, 3):
        field = QuadraticField(prime)
        matrix_count, survivors = guard_control(field)
        counts = [scalar_restriction_control(field, survivors, a, b)
                  for a, b in ((1, prime), (0, 0), (0, 1))]
        print(f"F{prime**2}: {matrix_count} invertible matrices, {len(survivors)} fixed by guard, "
              f"scalar-restriction counts {counts}, rank-one cone punctured size {cone_control(field)}")
    print("F2 coordinate-algebra automorphisms in dimension 3", coordinate_algebra_control())


if __name__ == '__main__':
    main()
