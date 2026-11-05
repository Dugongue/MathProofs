"""Exact diagnostics for the multiplicity and original-coordinate determinant formulas."""

from itertools import product
from pathlib import Path
import json
import random


Q = 3
ZERO = (0, 0)
ONE = (1, 0)


def mul(a, b):
    x, y = a
    u, v = b
    return ((x * u - y * v) % Q, (x * v + y * u) % Q)


def sub(a, b):
    return tuple((x - y) % Q for x, y in zip(a, b))


def power(a, exponent):
    result = ONE
    for _ in range(exponent):
        result = mul(result, a)
    return result


def det9(matrix):
    work = [row[:] for row in matrix]
    determinant = ONE
    for i in range(len(work)):
        pivot = next((j for j in range(i, len(work)) if work[j][i] != ZERO), None)
        if pivot is None:
            return ZERO
        if pivot != i:
            work[i], work[pivot] = work[pivot], work[i]
            determinant = sub(ZERO, determinant)
        scale = work[i][i]
        determinant = mul(determinant, scale)
        inverse = power(scale, 7)
        for j in range(i + 1, len(work)):
            factor = mul(work[j][i], inverse)
            work[j] = [sub(x, mul(factor, y)) for x, y in zip(work[j], work[i])]
    return determinant


def det3(matrix):
    work = [row[:] for row in matrix]
    determinant = 1
    for i in range(len(work)):
        pivot = next((j for j in range(i, len(work)) if work[j][i]), None)
        if pivot is None:
            return 0
        if pivot != i:
            work[i], work[pivot] = work[pivot], work[i]
            determinant = -determinant
        scale = work[i][i]
        determinant = determinant * scale % Q
        for j in range(i + 1, len(work)):
            factor = work[j][i] * pow(scale, -1, Q) % Q
            if factor:
                work[j] = [(x - factor * y) % Q for x, y in zip(work[j], work[i])]
    return determinant % Q


def f3_matrix(h, frobenius):
    size = len(h)
    out = [[0] * (2 * size) for _ in range(2 * size)]
    for i, j in product(range(size), repeat=2):
        for k, unit in enumerate([ONE, (0, 1)]):
            x, y = mul(h[i][j], power(unit, 3) if frobenius else unit)
            out[2 * i][2 * j + k] = x
            out[2 * i + 1][2 * j + k] = y
    return out


def norm_controls():
    rng = random.Random(3419)
    checks = 0
    for size in range(1, 4):
        for _ in range(18):
            while True:
                h = [[tuple(rng.randrange(Q) for _ in range(2)) for _ in range(size)]
                     for _ in range(size)]
                det_h = det9(h)
                if det_h != ZERO:
                    break
            norm = power(det_h, 4)
            assert norm[1] == 0
            for repeated in range(1, 4):
                for frobenius in (False, True):
                    block = f3_matrix(h, frobenius)
                    width = len(block)
                    dimension = repeated * width
                    actual = [[0] * dimension for _ in range(dimension)]
                    for b in range(repeated):
                        for i in range(width):
                            actual[b * width + i][b * width:b * width + width] = block[i]
                    calibration = (-1) ** (size * repeated) if frobenius else 1
                    assert det3(actual) == calibration * pow(norm[0], repeated, Q) % Q
                    checks += 1
    return checks


def rank_sparse(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = min(row)
            if pivot not in pivots:
                inverse = pow(row[pivot], -1, Q)
                pivots[pivot] = {k: v * inverse % Q for k, v in row.items()}
                break
            factor = row[pivot]
            for k, v in pivots[pivot].items():
                new = (row.get(k, 0) - factor * v) % Q
                if new:
                    row[k] = new
                else:
                    row.pop(k, None)
    return len(pivots)


def amplification_control():
    n, b = 3, 2
    slice_entries = [(i, i, i) for i in range(n)]
    slice_entries += [(n, i, j) for i, j in product(range(n), repeat=2)]
    matrix_entries = [(i * b + j, j * b + k, k * b + i)
                      for i, j, k in product(range(b), repeat=3)]
    sizes = [(n + 1) * b * b, n * b * b, n * b * b]
    entries = {tuple(x * b * b + y for x, y in zip(u, v))
               for u in slice_entries for v in matrix_entries}
    offsets = [0, sizes[0] ** 2, sizes[0] ** 2 + sizes[1] ** 2]

    def rows(i, j):
        for point in product(*(range(d) for d in sizes)):
            row = {}
            for mode, sign in ((i, 1), (j, -1)):
                other = list(point)
                for k in range(sizes[mode]):
                    other[mode] = k
                    if tuple(other) in entries:
                        row[offsets[mode] + k * sizes[mode] + point[mode]] = sign % Q
            yield row

    pair_dimensions = [sizes[i] ** 2 + sizes[j] ** 2 - rank_sparse(rows(i, j))
                       for i, j in [(0, 1), (0, 2), (1, 2)]]
    centroid = sum(d * d for d in sizes) - rank_sparse(
        row for i, j in [(0, 1), (0, 2)] for row in rows(i, j))
    assert pair_dimensions == [4, 4, 4]
    assert centroid == 1
    return {"format": sizes, "pair_adjoint_dimensions": pair_dimensions,
            "centroid_dimension": centroid}


def main():
    result = {"status": "PASS", "nonsplit_norm_and_frobenius_checks": norm_controls(),
              "amplified_scalar_centroid_fixture": amplification_control(),
              "scope": "Finite arithmetic diagnostics for the informal proof"}
    Path(__file__).with_name("CONTROLS.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
