"""Check the finite cases in the Kaspers-Pott design comparison."""

from itertools import product


def galois_ring_prime_or_quadratic(p, degree):
    """Use Z/p^2 or Z/9[t]/(t^2+1) with coordinatewise addition."""
    modulus = p * p
    points = list(product(range(modulus), repeat=degree))
    zero = (0,) * degree
    one = (1,) + (0,) * (degree - 1)

    def add(x, y):
        return tuple((a + b) % modulus for a, b in zip(x, y))

    def multiply(x, y):
        if degree == 1:
            return (x[0] * y[0] % modulus,)
        a, b = x
        c, d = y
        return ((a * c - b * d) % modulus, (a * d + b * c) % modulus)

    def power(x, exponent):
        out = one
        for _ in range(exponent):
            out = multiply(out, x)
        return out

    return points, zero, one, add, multiply, power


def blocks(p, degree):
    q = p**degree
    points, zero, one, add, multiply, power = galois_ring_prime_or_quadratic(p, degree)
    teichmuller = [x for x in points if x != zero and power(x, q) == x]
    squares = {multiply(x, x) for x in teichmuller}
    assert len(teichmuller) == q - 1
    assert len(squares) == (q - 1) // 2
    base = {frozenset(multiply(c, x) for x in squares) for c in points if c != zero}
    assert len(base) == 2 * (q + 1)
    assert set().union(*base) == set(points) - {zero}
    full = {frozenset(add(x, shift) for x in block) for shift in points for block in base}
    assert len(full) == 2 * q**2 * (q + 1)
    assert {len(block) for block in full} == {(q - 1) // 2}
    return full, zero, one, (p,) + (0,) * (degree - 1)


def through(block_set, first, second):
    return [block for block in block_set if first in block and second in block]


def largest_proper_intersection(block_set, block):
    return max(len(block & other) for other in block_set if other != block)


def main():
    block_set, zero, one, uniformizer = blocks(3, 2)
    counts = []
    for second in [one, uniformizer]:
        incident = through(block_set, zero, second)
        assert len(incident) == 3
        counts.append(sum(all(block.isdisjoint(other) for block in incident) for other in block_set))
    assert counts == [1047, 1026]
    print(f"q=9: disjoint-block counts for the two pairs are {counts}.")

    block_set, zero, one, uniformizer = blocks(11, 1)
    profiles = []
    for second in [one, uniformizer]:
        incident = through(block_set, zero, second)
        assert len(incident) == 4
        profiles.append(sorted(largest_proper_intersection(block_set, block) for block in incident))
    assert profiles == [[2] * 4, [3] * 4]
    print(f"q=11: maximal-intersection profiles are {profiles}.")


if __name__ == "__main__":
    main()
