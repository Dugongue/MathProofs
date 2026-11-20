"""Exact orbit-sum enumeration for the two-, three- and four-pigeon cases."""

from itertools import combinations, combinations_with_replacement, permutations
from math import gcd, lcm, prod


def orbit_ideals(n):
    holes = n - 1
    entries = tuple((i, j) for i in range(n) for j in range(holes))
    labels = tuple((i,) for i in range(n)) + tuple(
        (i, k, j) for i, k in combinations(range(n), 2) for j in range(holes)
    )
    label_index = {label: k for k, label in enumerate(labels)}
    actions = []
    for rows in permutations(range(n)):
        for cols in permutations(range(holes)):
            image = tuple(rows[i] * holes + cols[j] for i, j in entries)
            label_image = tuple(rows[i] for i in range(n)) + tuple(
                label_index[(*sorted((rows[i], rows[k])), cols[j])]
                for i, k, j in labels[n:]
            )
            actions.append((image, label_image))

    assignments_seen = set()
    denominators = [1] * n
    for mask in range(1 << len(entries)):
        if mask in assignments_seen:
            continue
        occupied = tuple(i for i in range(len(entries)) if mask & (1 << i))
        stabilizer = []
        for image, label_image in actions:
            changed = sum(1 << image[i] for i in occupied)
            assignments_seen.add(changed)
            if changed == mask:
                stabilizer.append(label_image)
        matrix = tuple(tuple(int(bool(mask & (1 << (i * holes + j))))
                             for j in range(holes)) for i in range(n))
        values = tuple(sum(row) - 1 for row in matrix) + tuple(
            matrix[i][j] * matrix[k][j] for i, k, j in labels[n:]
        )
        active = tuple(i for i, value in enumerate(values) if value != 0)
        divisor = 0
        for degree in range(1, n + 1):
            monomials_seen = set()
            if divisor != 1:
                for monomial in combinations_with_replacement(active, degree):
                    if monomial in monomials_seen:
                        continue
                    orbit = {
                        tuple(sorted(action[i] for i in monomial))
                        for action in stabilizer
                    }
                    monomials_seen.update(orbit)
                    value = len(orbit) * prod(values[i] for i in monomial)
                    divisor = gcd(divisor, value)
                    if divisor == 1:
                        break
            denominators[degree - 1] = lcm(denominators[degree - 1], divisor)
    return denominators


if __name__ == "__main__":
    for pigeons in range(2, 5):
        actual = orbit_ideals(pigeons)
        full = lcm(*range(1, pigeons + 1))
        expected = [full // lcm(*range(1, d + 1)) for d in range(1, pigeons + 1)]
        assert actual == expected, (pigeons, actual, expected)
        print(f"{pigeons} pigeons: {actual}")
