"""Exact finite tests of the probe mark and the projective correction."""

import json
import random


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(matrix):
    return [list(row) for row in zip(*matrix)]


def multiply(left, right, p):
    return [[sum(x * y for x, y in zip(row, col)) % p
             for col in transpose(right)] for row in left]


def eliminate(matrix, p, inverse=False):
    n = len(matrix)
    rows = [row[:] + (eye(n)[i] if inverse else []) for i, row in enumerate(matrix)]
    det = 1
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j] % p), None)
        if pivot is None:
            if inverse:
                raise ValueError("singular matrix")
            return 0
        if pivot != j:
            rows[pivot], rows[j] = rows[j], rows[pivot]
            det = -det
        entry = rows[j][j] % p
        det = det * entry % p
        rows[j] = [c * pow(entry, -1, p) % p for c in rows[j]]
        for i in range(n):
            if i != j:
                factor = rows[i][j]
                rows[i] = [(a - factor * b) % p for a, b in zip(rows[i], rows[j])]
    return [row[n:] for row in rows] if inverse else det


def invertible(n, p, rng):
    while True:
        m = [[rng.randrange(p) for _ in range(n)] for _ in range(n)]
        if eliminate(m, p):
            return m


def triangular(kernel, quotient, p, rng):
    h = len(kernel)
    k = len(quotient)
    return [
        row + [rng.randrange(p) for _ in range(k)] for row in kernel
    ] + [[0] * h + row for row in quotient]


def pf(matrix, p):
    if not matrix:
        return 1
    result = 0
    for j in range(1, len(matrix)):
        indexes = [i for i in range(1, len(matrix)) if i != j]
        sub = [[matrix[i][k] for k in indexes] for i in indexes]
        result += (-1) ** (j + 1) * matrix[0][j] * pf(sub, p)
    return result % p


def scaled_congruence(qt, dl, dr, eta, p):
    base = multiply(multiply(transpose(dl), qt, p), dr, p)
    return [[eta * entry % p for entry in row] for row in base]


def frame_pair(r, k, p, rng):
    source = invertible(r+k, p, rng)
    target = invertible(r+k, p, rng)
    ker = invertible(r, p, rng)
    quot = invertible(k, p, rng)
    d = triangular(ker, quot, p, rng)
    adapted = multiply(multiply(target, d, p), eliminate(source, p, True), p)
    return eliminate(ker, p), quot, eliminate(source, p), eliminate(target, p), eliminate(adapted, p)


def check(p, rng):
    counts = {"rectangular_frame_cases": 0, "alternating_frame_cases": 0,
              "symmetric_lagrangian_cases": 0, "dual_correction_essential_cases": 0}
    for k in range(1, 7):
        for r in range(4):
            for s in range(4):
                for eta in range(1, p):
                    a, dl, ds, dt, full_l = frame_pair(r, k, p, rng)
                    b, dr, es, et, full_r = frame_pair(s, k, p, rng)
                    qt = invertible(k, p, rng)
                    qs = scaled_congruence(qt, dl, dr, eta, p)
                    ms = eliminate(qs, p) * pow(ds * es % p, -1, p) % p
                    mt = eliminate(qt, p) * pow(dt * et % p, -1, p) % p
                    good = full_l * full_r * mt % p
                    assert a * b * ms * pow(eta, -k, p) % p == good
                    if a * b * ms * pow(eta, k, p) % p != good:
                        counts["dual_correction_essential_cases"] += 1
                    counts["rectangular_frame_cases"] += 1

    for k in (2, 4, 6):
        for r in range(4):
            for eta in range(1, p):
                for _ in range(12):
                    a, d, ds, dt, full = frame_pair(r, k, p, rng)
                    qt = [[int(i + 1 == j and i % 2 == 0)
                           - int(j + 1 == i and j % 2 == 0)
                           for j in range(k)] for i in range(k)]
                    qs = scaled_congruence(qt, d, d, eta, p)
                    ms = pf(qs, p) * pow(ds, -1, p) % p
                    mt = pf(qt, p) * pow(dt, -1, p) % p
                    assert a * ms * pow(eta, -(k//2), p) % p == full * mt % p
                    counts["alternating_frame_cases"] += 1

    for m in range(1, 6):
        for eta in range(1, p):
            for swap in (False, True):
                d = invertible(m, p, rng)
                dual = [[x * pow(eta, -1, p) % p for x in row]
                        for row in transpose(eliminate(d, p, True))]
                zero = [[0] * m for _ in range(m)]
                top = [a + b for a, b in zip(d, zero)]
                bottom = [a + b for a, b in zip(zero, dual)]
                hy = top + bottom if not swap else bottom + top
                form = [[int(abs(i-j) == m) for j in range(2*m)] for i in range(2*m)]
                assert scaled_congruence(form, hy, hy, eta, p) == form
                assert eliminate(hy, p) == (-1 if swap else 1)**m * pow(eta, -m, p) % p
                counts["symmetric_lagrangian_cases"] += 1
    return counts


if __name__ == "__main__":
    generator = random.Random(730321)
    results = {str(p): check(p, generator) for p in (3, 5, 7)}
    print(json.dumps(results, indent=2))
