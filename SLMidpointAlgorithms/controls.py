"""Small exhaustive checks for selected identities in the informal proofs."""

from itertools import product
import json
from pathlib import Path


def add(x, y, p):
    return tuple((a + b) % p for a, b in zip(x, y))


def sub(x, y, p):
    return tuple((a - b) % p for a, b in zip(x, y))


def mv(matrix, vector, p):
    return tuple(sum(a * b for a, b in zip(row, vector)) % p for row in matrix)


def span(vectors, dim, p):
    values = {(0,) * dim}
    for vector in vectors:
        values = {add(x, tuple(c * a for a in vector), p)
                  for x in values for c in range(p)}
    return values


def check_flag_elimination():
    rows = list(product(range(2), repeat=2))
    matrices = list(product(rows, repeat=3))
    count = 0
    for a in matrices:
        flags = [span(a[:i], 2, 2) for i in range(3)]
        orbit = set(product(*[
            tuple(add(a[i], v, 2) for v in flags[i]) for i in range(3)
        ]))
        explicit = set()
        for x, y, z in product(range(2), repeat=3):
            u = ((1, 0, 0), (x, 1, 0), (y, z, 1))
            columns = [mv(u, column, 2) for column in zip(*a)]
            explicit.add(tuple(zip(*columns)))
        assert orbit == explicit
        for b in matrices:
            assert (b in explicit) == all(sub(b[i], a[i], 2) in flags[i] for i in range(3))
            count += 1
    return count


def invertible_2(p):
    for a, b, c, d in product(range(p), repeat=4):
        if (a * d - b * c) % p:
            yield ((a, b), (c, d))


def check_affine_blocks(p):
    # Tensor action in formats (3,1,1), with flag blocks (2,1) in mode one.
    # Couple the diagonal and translation choices by taking a graph
    # subgroup t = v - Mv, or allow every translation in the full group.
    point = (1, 1)
    top_vectors = list(product(range(p), repeat=2))
    vectors = list(product(range(p), repeat=3))
    total = 0
    for full_translation in (False, True):
        group = []
        for linear in invertible_2(p):
            translations = (top_vectors if full_translation
                            else [sub(point, mv(linear, point, p), p)])
            for x, y in translations:
                group.append((linear[0] + (x,), linear[1] + (y,), (0, 0, 1)))
        by_linear = {}
        for g in group:
            by_linear.setdefault(tuple(row[:2] for row in g[:2]), g)
        for suffix in range(p):
            zero = (0, 0, suffix)
            translation_values = {
                mv(g, zero, p)[:2] for g in group
                if tuple(row[:2] for row in g[:2]) == ((1, 0), (0, 1))
            }
            for x in vectors:
                if x[-1] != suffix:
                    continue
                expected_orbit = {mv(g, x, p)[:2] for g in group}
                predicted_orbit = {
                    add(mv(g, x, p)[:2], t, p)
                    for g in by_linear.values() for t in translation_values
                }
                assert expected_orbit == predicted_orbit
                for linear, lift in by_linear.items():
                    can_correct = sub(x[:2], mv(lift, x, p)[:2], p) in translation_values
                    has_stabilizer = any(
                        mv(g, x, p) == x and tuple(row[:2] for row in g[:2]) == linear
                        for g in group
                    )
                    assert can_correct == has_stabilizer
                    total += 1
    return total


def rank_and_det(matrix, p):
    rows = [list(row) for row in matrix]
    rank, det = 0, 1
    for col in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        if pivot != rank:
            rows[pivot], rows[rank] = rows[rank], rows[pivot]
            det = -det
        value = rows[rank][col]
        det = det * value % p
        inverse = pow(value, -1, p)
        for i in range(rank + 1, len(rows)):
            factor = rows[i][col] * inverse % p
            if factor:
                rows[i] = [(a - factor * b) % p for a, b in zip(rows[i], rows[rank])]
        rank += 1
    return rank, det % p if rank == len(rows) else 0


def check_pencil():
    n, p = 12, 3
    exponents = (0, 1, 4, 8)
    count = 0
    for a, b, d, e, c in product(range(p), repeat=5):
        coefficients = dict(zip(exponents, (a, b, d, e)))
        matrix = tuple(tuple((coefficients.get(i - j, 0) + c * (i == 0 and j == 1)) % p
                             for j in range(n)) for i in range(n))
        rank, det = rank_and_det(matrix, p)
        assert det == pow(a, n - 2, p) * (a * a - b * c) % p
        for exponent in (4, 8):
            assert (rank <= n - exponent + 1) == all(
                coefficients[i] == 0 for i in exponents if i < exponent
            )
        assert (rank <= 1) == all(value == 0 for value in coefficients.values())
        count += 1
    return count


def main():
    report = {
        "status": "PASS",
        "shared_row_pairs": check_flag_elimination(),
        "affine_block_linear_part_cases": {str(p): check_affine_blocks(p) for p in (2, 3)},
        "rank_band_and_determinant_pencil_checks": check_pencil(),
        "scope": "Exact finite checks of row, affine-block and pencil identities."
    }
    Path(__file__).with_name("CONTROLS.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(json.dumps(report))


if __name__ == "__main__":
    main()
