"""Exhaustively check local tensor transport on small cyclic module products."""

from collections import Counter
from itertools import product
from math import factorial


def matrix_choices(p, k, lengths):
    places = [(a, b) for a in lengths for b in lengths]
    ranges = [range(p ** max(0, min(a, b) - k)) for a, b in places]
    for digits in product(*ranges):
        yield tuple(
            (digit * p ** (k + max(a - b, 0))) % (p ** a)
            for digit, (a, b) in zip(digits, places)
        )


def matrix_product(left, right):
    return tuple(
        sum(left[2 * i + t] * right[2 * t + j] for t in range(2))
        for i, j in product(range(2), repeat=2)
    )


def exponential(matrix, p, precision):
    modulus = p ** precision
    power = (1, 0, 0, 1)
    result = power
    for m in range(1, 2 * precision + 1):
        power = matrix_product(power, matrix)
        unit = factorial(m)
        p_part = 1
        while unit % p == 0:
            unit //= p
            p_part *= p
        assert all(entry % p_part == 0 for entry in power)
        inverse = pow(unit, -1, modulus)
        result = tuple(
            (old + entry // p_part * inverse) % modulus
            for old, entry in zip(result, power)
        )
    return result


def run_case(p, precision, lengths):
    k = 1 if p != 2 else 2
    moduli = [p ** a for a in lengths]
    places = list(product(range(2), repeat=2))
    identity = (1, 0, 0, 1)
    matrix_domain = tuple(matrix_choices(p, k, lengths))
    scalar_domain = tuple(range(0, p ** precision, p ** k))

    def reduce_matrix(matrix):
        return tuple(value % moduli[i] for value, (i, _) in zip(matrix, places))

    def act(matrix, tensor, scalar=1):
        return tuple(
            scalar * sum(matrix[2 * i + j] * tensor[j] for j in range(2))
            % moduli[i]
            for i in range(2)
        )

    def exp_scalar(x):
        return exponential((x, 0, 0, 0), p, precision)[0]

    def difference(left, right):
        return tuple((a - b) % modulus for a, b, modulus in zip(left, right, moduli))

    def at_depth(vector, depth):
        return tuple(x % (p ** min(a, depth)) for x, a in zip(vector, lengths))

    direct_matrices = {
        reduce_matrix(tuple(a + b for a, b in zip(identity, matrix)))
        for matrix in matrix_domain
    }
    exp_matrices = {
        matrix: reduce_matrix(exponential(matrix, p, precision))
        for matrix in matrix_domain
    }
    assert set(exp_matrices.values()) == direct_matrices
    exp_scalars = {x: exp_scalar(x) for x in scalar_domain}
    assert set(exp_scalars.values()) == {1 + x for x in scalar_domain}
    coordinates = tuple(product(range(moduli[0]), range(moduli[1])))
    local_group = tuple(product(direct_matrices, exp_scalars.values(), exp_scalars.values()))
    log_domain = tuple(product(matrix_domain, scalar_domain, scalar_domain))
    layer_checks = 0
    for source in coordinates:
        direct_images = Counter(act(g, source, u * v) for g, u, v in local_group)
        linear_stabilizer_size = 0
        for x, s, t in log_domain:
            linear = act(
                (x[0] + s + t, x[1], x[2], x[3] + s + t), source
            )
            image = act(exp_matrices[x], source, exp_scalars[s] * exp_scalars[t])
            displacement = difference(image, source)
            linear_stabilizer_size += linear == (0, 0)
            for j in range(k, precision):
                vanishes = at_depth(linear, j) == (0, 0)
                assert vanishes == (at_depth(displacement, j) == (0, 0))
                if vanishes:
                    assert at_depth(linear, j + 1) == at_depth(displacement, j + 1)
                layer_checks += 1
        assert direct_images[source] == linear_stabilizer_size
        assert set(direct_images.values()) == {linear_stabilizer_size}
    print(f"p={p}, e={precision}, lengths={lengths}, "
          f"group={len(local_group)}, tensors={len(coordinates)}, "
          f"layer checks={layer_checks}")
    return layer_checks


if __name__ == "__main__":
    cases = ((3, 2, (2, 2)), (3, 3, (1, 3)), (2, 3, (3, 3)), (2, 4, (2, 4)))
    print(f"Total verified layer checks: {sum(run_case(*case) for case in cases)}")
