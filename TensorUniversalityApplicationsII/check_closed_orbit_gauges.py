from itertools import product, permutations


def field_arithmetic(prime):
    # F4 uses x^2+x+1 and F9 uses x^2+1.
    linear = 1 if prime == 2 else 0

    def add(a, b):
        return (a + b) % prime + ((a // prime + b // prime) % prime) * prime

    def multiply(a, b):
        u, x = a % prime, a // prime
        v, y = b % prime, b // prime
        return (u * v - x * y) % prime + ((u * y + x * v - linear * x * y) % prime) * prime

    def power(x, degree):
        answer = 1
        for _ in range(degree):
            answer = multiply(answer, x)
        return answer

    return add, multiply, power


def check(prime):
    order = prime ** 2
    add, mul, power = field_arithmetic(prime)

    def sum_values(values):
        result = 0
        for value in values:
            result = add(result, value)
        return result

    def negative(value):
        return mul(prime - 1, value)

    def identity(size):
        return tuple(tuple(int(i == j) for j in range(size)) for i in range(size))

    def apply(matrix, vector):
        return tuple(sum_values(mul(a, b) for a, b in zip(row, vector)) for row in matrix)

    def columns(matrix):
        return tuple(zip(*matrix))

    def multiply_matrix(left, right):
        return columns(tuple(apply(left, col) for col in columns(right)))

    def determinant(matrix):
        size = len(matrix)
        answer = 0
        for cols in permutations(range(size)):
            term = 1
            for row, col in enumerate(cols):
                term = mul(term, matrix[row][col])
            odd = sum(cols[i] > cols[j] for i in range(size) for j in range(i + 1, size)) % 2
            answer = add(answer, negative(term) if odd else term)
        return answer

    def times_polynomial(left, right):
        result = [0] * (len(left) + len(right) - 1)
        for i, a in enumerate(left):
            for j, b in enumerate(right):
                result[i+j] = add(result[i+j], mul(a, b))
        return tuple(result)

    def symmetric_power(g, degree):
        x, y = columns(g)
        evaluated = []
        for i in range(degree + 1):
            term = (1,)
            for factor in (x,) * (degree - i) + (y,) * i:
                term = times_polynomial(term, factor)
            evaluated.append(term)
        return columns(evaluated)

    def shear(size, left, right, value):
        matrix = [list(row) for row in identity(size)]
        matrix[left][right] = value
        return tuple(map(tuple, matrix))

    def basis(size):
        return columns(identity(size))

    def inverse2(g):
        (a, b), (c, d) = g
        return (d, negative(b)), (negative(c), a)

    def frobenius(g, exponent):
        return tuple(tuple(power(value, exponent) for value in row) for row in g)

    candidates = [((a, b), (c, d)) for a, b, c, d in product(range(order), repeat=4)
                  if add(mul(a, d), negative(mul(b, c))) == 1]
    assert len(candidates) == order * (order ** 2 - 1)
    checks = 0
    for index, g in enumerate(candidates):
        g_inverse = inverse2(g)
        h = {1: g}
        h_inverse = {1: g_inverse}
        B = {1: identity(2)}
        for degree in range(2, prime + 1):
            size = degree + 1
            first, second = index % order, (index + 1) % order
            h[degree] = multiply_matrix(shear(size, 0, 1, first), shear(size, 1, size-1, second))
            h_inverse[degree] = multiply_matrix(shear(size, 1, size-1, negative(second)),
                                                shear(size, 0, 1, negative(first)))

            def transported(left, right):
                return apply(h[degree], times_polynomial(apply(g_inverse, left),
                                                          apply(h_inverse[degree-1], right)))

            # Recover every degree-r monomial using only the transported multiplication.
            x, y = basis(2)
            recovered = [transported(x, col) for col in columns(B[degree-1])]
            recovered.append(transported(y, columns(B[degree-1])[-1]))
            B[degree] = columns(recovered)
            assert B[degree] == multiply_matrix(h[degree], symmetric_power(g_inverse, degree))
            assert determinant(B[degree]) == 1
            for left, right in product(basis(2), basis(degree)):
                assert transported(left, apply(B[degree-1], right)) == apply(
                    B[degree], times_polynomial(left, right))
                checks += 1

        # Include a distinct next level to test the order of the cyclic factors.
        next_inverse = inverse2(candidates[(index * 17 + 3) % len(candidates)])
        pure_columns = columns((basis(prime+1)[0], basis(prime+1)[-1]))
        transported_link = multiply_matrix(h[prime], multiply_matrix(pure_columns, next_inverse))
        B_inverse = multiply_matrix(symmetric_power(g, prime), h_inverse[prime])
        C = multiply_matrix(frobenius(g, prime), next_inverse)
        assert multiply_matrix(B_inverse, transported_link) == multiply_matrix(pure_columns, C)
        assert determinant(C) == 1
        checks += 1

        # Verify a Lang coset fiber for two unrelated changes of basis.
        next_g = inverse2(next_inverse)
        left_link = multiply_matrix(frobenius(g, prime), g_inverse)
        right_link = multiply_matrix(frobenius(next_g, prime), next_inverse)
        ratio = multiply_matrix(next_inverse, g)
        assert (left_link == right_link) == (frobenius(ratio, prime) == ratio)
        checks += 1

    # Fixing the one-dimensional source/complement projector gives the expected GL1 group.
    projector = ((1, 0), (0, 0))
    for exponent in (prime, order):
        stabilized = [g for g in candidates if g == frobenius(g, exponent)
                      and multiply_matrix(g, projector) == multiply_matrix(projector, g)]
        assert len(stabilized) == exponent - 1
    return len(candidates), checks


if __name__ == '__main__':
    cases = [check(prime) for prime in (2, 3)]
    print(f'PASS: {sum(n for n, _ in cases)} changes of basis and '
          f'{sum(n for _, n in cases)} normalization and Lang-link identities over F4 and F9')
