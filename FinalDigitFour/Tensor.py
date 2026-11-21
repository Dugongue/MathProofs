"""Exact finite controls for the fully symmetric final-digit construction."""

from collections import defaultdict
from itertools import permutations, product


def field_form(scalar):
    sizes = (2, 2, 2)
    n = sum(sizes)
    cursor = 0
    parts = []
    for i, size in enumerate(sizes, start=1):
        x = tuple(range(cursor, cursor + size))
        dual = tuple(range(cursor + size, cursor + 2 * size))
        cursor += 2 * size
        h = tuple(range(cursor, cursor + (2**i) * (n + 7)))
        cursor += len(h)
        parts.append((x, dual, h))
    markers = tuple(range(cursor, cursor + 3))
    dimension = cursor + 3
    terms = {}

    def assign(indices, coefficient):
        if coefficient:
            for order in set(permutations(indices)):
                terms[order] = coefficient

    assign(tuple(x[0] for x, _, _ in parts), scalar)
    for (x, dual, h), marker in zip(parts, markers):
        for u, v in zip(x, dual):
            assign((marker, u, v), 1)
        for u, v in zip(h[::2], h[1::2]):
            assign((marker, u, v), 1)
    return terms, dimension, parts, markers


def rank(entries, p):
    rows = defaultdict(dict)
    for (i, j), coefficient in entries.items():
        if coefficient % p:
            rows[i][j] = coefficient % p
    pivots = {}
    for row in rows.values():
        while row:
            j = min(row)
            value = row[j]
            if j not in pivots:
                pivots[j] = {k: c * pow(value, -1, p) % p for k, c in row.items()}
                break
            for k, c in pivots[j].items():
                new = (row.get(k, 0) - value * c) % p
                if new:
                    row[k] = new
                else:
                    row.pop(k, None)
    return len(pivots)


def slice_matrix(terms, vector, p, limit):
    entries = defaultdict(int)
    for (i, j, k), coefficient in terms.items():
        if j < limit and k < limit:
            entries[j, k] += coefficient * vector.get(i, 0)
    return {position: value % p for position, value in entries.items() if value % p}


def ring_table(terms, dimension, p, exponent):
    n = 2 * dimension + 2
    n += n % p == 0
    top = n - 1
    place = p ** (exponent - 1)
    table = defaultdict(dict)

    def place_entry(i, j, out, value):
        table[i, j][out] = value
        table[j, i][out] = value

    for i in range(n):
        place_entry(0, i, i, 1)
    for i in range(1, dimension + 1):
        place_entry(i, i + dimension, top, 1)
    if top == 2 * dimension + 2:
        place_entry(top - 1, top - 1, top, 1)
    for (i, j, k), coefficient in terms.items():
        place_entry(i + 1, j + 1, k + dimension + 1, place * coefficient)
    return table, n, top, p**exponent, place


def check_products(table, n, top, modulus):
    indexed = defaultdict(list)
    for (i, j), result in table.items():
        indexed[i].append((j, result))
    left = defaultdict(int)
    for (i, j), result in table.items():
        assert table[j, i] == result
        for middle, value in result.items():
            for k, next_result in indexed[middle]:
                for output, weight in next_result.items():
                    left[i, j, k, output] += value * weight

    left = {entry: value % modulus for entry, value in left.items() if value % modulus}
    assert left == {(k, j, i, out): c for (i, j, k, out), c in left.items()}
    traces = [0] * n
    for (i, j), result in table.items():
        traces[i] += result.get(j, 0)
    assert traces == [n] + [0] * (n - 1)
    form = {(i, j, k): value for (i, j, k, out), value in left.items() if out == top}
    for triple, coefficient in form.items():
        assert all(form.get(order) == coefficient for order in permutations(triple))
    gram = {(j, k): c for (i, j, k), c in form.items() if i == 0}
    assert len(gram) == n and all(value == 1 for value in gram.values())
    assert len({i for i, _ in gram}) == len({j for _, j in gram}) == n
    for mode in range(3):
        contraction = {
            triple[:mode] + triple[mode + 1:]: c
            for triple, c in form.items()
            if triple[mode] == 0
        }
        assert contraction == gram
    return form


def main():
    checks = 0
    for p, exponent in ((2, 2), (2, 3), (3, 2), (5, 2)):
        ring_forms = []
        for scalar in (0, 1):
            terms, dimension, parts, markers = field_form(scalar)
            n = sum(len(x) for x, _, _ in parts)
            k_dimension = markers[0]
            for support in product((0, 1), repeat=3):
                vector = dict(zip(markers, support))
                for extra in ({}, {parts[0][0][0]: 1}, {parts[1][2][0]: 1}):
                    point = vector | extra
                    full_rank = rank(slice_matrix(terms, point, p, dimension), p)
                    assert (full_rank <= n + 6) == (not any(support))
                    restricted_rank = rank(slice_matrix(terms, point, p, k_dimension), p)
                    base = sum(len(h) for (_, _, h), flag in zip(parts, support) if flag)
                    assert base <= restricted_rank <= base + 2 * n
                    checks += 1
            table, size, top, modulus, place = ring_table(terms, dimension, p, exponent)
            assert size % p
            form = check_products(table, size, top, modulus)
            radical_triples = {
                (i, j, k): c for (i, j, k), c in form.items() if min(i, j, k) > 0
            }
            assert radical_triples == {
                (i + 1, j + 1, k + 1): place * c for (i, j, k), c in terms.items()
            }
            ring_forms.append({pos: c % place for pos, c in form.items() if c % place})
        assert ring_forms[0] == ring_forms[1]
    print(f"{checks} rank-band checks, 8 algebra/slice checks, 4 common-reduction checks")


if __name__ == "__main__":
    main()
