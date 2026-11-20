
"""Exhaustive small tests of the modular symmetric PHP degree formula."""

from itertools import combinations, permutations, product


def p_part(size, p):
    power = 1
    while size % p == 0:
        power *= p
        size //= p
    return power


def action_tables(n):
    rows, cols = range(n), range(n - 1)
    labels = [(i,) for i in rows]
    labels += [(i, j, h) for i, j in combinations(rows, 2) for h in cols]
    label_index = {label: k for k, label in enumerate(labels)}
    tables = []
    for row, col in product(permutations(rows), permutations(cols)):
        cells = tuple(row[i] * (n - 1) + col[h] for i in rows for h in cols)
        renamed = []
        for label in labels:
            if len(label) == 1:
                new_label = (row[label[0]],)
            else:
                i, j, h = label
                a, b = sorted((row[i], row[j]))
                new_label = (a, b, col[h])
            renamed.append(label_index[new_label])
        tables.append((cells, tuple(renamed)))
    return labels, tables


def values(matrix, n, labels, p):
    rows = [matrix[i * (n - 1):(i + 1) * (n - 1)] for i in range(n)]
    return tuple(
        (sum(rows[label[0]]) - 1) % p if len(label) == 1
        else rows[label[0]][label[2]] * rows[label[1]][label[2]]
        for label in labels
    )


def label_orbits(active, stabilizer):
    unseen = set(active)
    while unseen:
        i = min(unseen)
        orbit = {perm[i] for perm in stabilizer}
        assert orbit <= unseen
        unseen -= orbit
        yield orbit


def direct_orbit_certificate_degree(active, stabilizer, evaluations, p):
    """Search invariant squarefree orbit sums and check their evaluations."""
    for degree in range(1, len(active) + 1):
        for support in combinations(active, degree):
            orbit = {
                tuple(sorted(perm[i] for i in support)) for perm in stabilizer
            }
            value = sum(product_of(evaluations[i] for i in term)
                        for term in orbit) % p
            if value:
                inverse = pow(value, -1, p)
                assert sum(inverse * product_of(evaluations[i] for i in term)
                           for term in orbit) % p == 1
                return degree
    raise AssertionError("a product over all active placeholders must work")


def product_of(items):
    result = 1
    for item in items:
        result *= item
    return result


def check():
    table = []
    for n in (2, 3, 4):
        labels, actions = action_tables(n)
        maxima = {p: 0 for p in (2, 3, 5)}
        count = 0
        for matrix in product((0, 1), repeat=n * (n - 1)):
            stabilizer = [
                perm for cells, perm in actions
                if all(matrix[i] == matrix[j] for i, j in enumerate(cells))
            ]
            for p in maxima:
                evaluations = values(matrix, n, labels, p)
                active = [i for i, value in enumerate(evaluations) if value]
                local = min(p_part(len(orbit), p)
                            for orbit in label_orbits(active, stabilizer))
                if n <= 3:
                    assert local == direct_orbit_certificate_degree(
                        active, stabilizer, evaluations, p
                    )
                maxima[p] = max(maxima[p], local)
            count += 1
        for p, degree in maxima.items():
            bound = 1
            while p * bound <= n:
                bound *= p
            assert degree == bound
            table.append((n, p, count, degree))
    print("pigeons  characteristic  assignments  max local degree")
    for n, p, count, degree in table:
        print(f"{n:7}  {p:14}  {count:11}  {degree:16}")


if __name__ == "__main__":
    check()
