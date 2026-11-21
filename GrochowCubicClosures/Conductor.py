"""Finite checks for the monomial conductor and characteristic-three chart."""
from functools import lru_cache
from itertools import product


def minimum_cost(exponents, single, pair):
    """Compute the least s-power by actual monomial divisibility."""
    m = len(exponents)
    units = [tuple(int(i == j) for i in range(m)) for j in range(m)]
    shifts = [(unit, single) for unit in units]
    shifts += [(tuple(3 * value for value in unit), 0) for unit in units]
    if pair is not None:
        for i, first in enumerate(units):
            for second in units[i:]:
                shifts.append((tuple(a + b for a, b in zip(first, second)), pair))

    @lru_cache(maxsize=None)
    def search(alpha):
        if not any(alpha):
            return 0
        return min(weight + search(rest) for shift, weight in shifts
                   if all(value >= delta for value, delta in zip(alpha, shift))
                   for rest in [tuple(value - delta for value, delta in zip(alpha, shift))])

    return search(exponents)


def check_conductor():
    checked = 0
    for m in (1, 2, 3):
        residues = list(product(range(3), repeat=m))
        for single in (1, 2, 3):
            for pair in (None, *range(single, 2 * single + 3)):
                expected = m * (2 * single if pair is None else min(2 * single, pair))
                minimum = {alpha: minimum_cost(alpha, single, pair)
                           for alpha in product(range(5), repeat=m)}
                for alpha in residues:
                    worst = max(minimum[tuple(a + b for a, b in zip(alpha, beta))]
                                for beta in residues)
                    assert worst == expected, (m, single, pair, alpha, worst, expected)
                    checked += 1
    print(f"{checked} conductor thresholds verified by monomial enumeration.")


def check_expansion():
    for a, q, l, b, z, t in product(range(3), repeat=6):
        actual = a + (z + t) * q + (z + t) ** 2 * l + b * (z + t) ** 3
        expected = a + z * q + z * z * l + b * z ** 3 + (q + 2 * z * l) * t + l * t * t + b * t ** 3
        assert (actual - expected) % 3 == 0
    print("All 729 coefficient evaluations of the cubic chart over F3 passed.")


if __name__ == "__main__":
    check_conductor()
    check_expansion()
