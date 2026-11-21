"""Finite coefficient checks for the explicit border decomposition."""
from itertools import product


def convolution(left, right, modulus):
    out = [0] * (len(left) + len(right) - 1)
    for i, u in enumerate(left):
        for j, v in enumerate(right):
            out[i + j] = (out[i + j] + u * v) % modulus
    return out


def cube(coefficients, modulus):
    return convolution(convolution(coefficients, coefficients, modulus), coefficients, modulus)


def check(modulus, m):
    a = next(a for a in range(1, modulus)
             if is_unit(a, modulus) and is_unit(m + a, modulus))
    c = (m + a) % modulus
    inv_a = pow(a, -1, modulus)
    inv_c = pow(c, -1, modulus)
    params = range(min(modulus, 4))
    count = 0
    for coordinates in product(params, repeat=m):
        forms = tuple(coordinates) + (-inv_a * sum(coordinates) % modulus,)
        weights = (1,) * m + (a,)
        second_moment = (sum(x * x for x in coordinates)
                         + inv_a * sum(coordinates)**2) % modulus
        for r, z in product(params, repeat=2):
            value = [0] * 7
            for weight, ell in zip(weights, forms):
                for i, coefficient in enumerate(cube((r, ell), modulus)):
                    value[i] += weight * coefficient
            for i, coefficient in enumerate(cube((r, 0, -inv_c * z), modulus)):
                value[i] -= c * coefficient
            assert value[0] % modulus == value[1] % modulus == 0
            assert value[2] % modulus == (3 * r * second_moment + 3 * r * r * z) % modulus
            count += 1
    return count


def is_unit(value, modulus):
    from math import gcd
    return gcd(value, modulus) == 1


def main():
    total = sum(check(modulus, m) for modulus in (5, 7, 25, 49) for m in (2, 4))
    print(f"{total} exact constant, linear and quadratic coefficient checks")


if __name__ == "__main__":
    main()
