"""Numerical controls for the explicit noisy Choi reconstruction (NumPy)."""
from itertools import combinations, permutations

import numpy as np


def template(n, edges):
    d = 3 * n * n
    pairs = list(combinations(range(n), 2))
    weights = (-5, -3, -1, 1, 3, 5)
    marker = np.zeros((d, d), dtype=int)

    def connect(i, j, weight):
        marker[i, j] -= weight
        marker[j, i] -= weight
        marker[i, i] += weight
        marker[j, j] += weight

    for i in range(n):
        plus, minus, zero = 3 * i, 3 * i + 1, 3 * i + 2
        for left, right, weight in (
            (plus, minus, 1000 * n), (plus, zero, 2000 * n), (minus, zero, 4000 * n)
        ):
            connect(left, right, weight)
    for k, pair in enumerate(pairs):
        start = 3 * n + 6 * k
        for port, w in enumerate(weights):
            for i in pair:
                connect(start + port, 3 * i, 20 + w)
                connect(start + port, 3 * i + 1, 20 - w)
        v = np.array((1, -1, 0, 0, -1, 1) if pair in edges else (1, -1, -1, 1, 0, 0))
        marker[start:start + 6, start:start + 6] += np.outer(v, v)

    s = 1 / (8 * n * d)
    b = (1 - s) / d**2
    alpha = (1 - s) / (360000 * n**6)
    rho = np.diag(b + alpha * marker.ravel())
    indices = np.arange(d) * (d + 1)
    rho[np.ix_(indices, indices)] += s / d
    return rho, b, alpha


def coordinate_basis(d):
    for i in range(d):
        a = np.zeros((d, d), dtype=complex)
        a[i, i] = 1
        yield a
    for i, j in combinations(range(d), 2):
        for value in (1, 1j):
            a = np.zeros((d, d), dtype=complex)
            a[i, j], a[j, i] = value, np.conjugate(value)
            yield a


def refine(p, d, first):
    shaped = p.reshape((d, d, d, d))
    cells = [np.eye(d)]
    for a in coordinate_basis(d):
        if first:
            b = np.einsum("jl,ilkj->ik", a, shaped)
        else:
            b = np.einsum("ik,kjil->jl", a, shaped)
        e, u = np.linalg.eigh(b)
        cuts = np.flatnonzero(np.diff(e) > 1 / (10 * d**2)) + 1
        intervals = [v @ v.conj().T for v in np.split(u, cuts, axis=1)]
        refined = [x @ y for x in cells for y in intervals]
        cells = [x for x in refined if x.trace().real > 0.5]
        if len(cells) == d:
            break
    assert len(cells) == d
    return cells


def recover(p, h, b, alpha, d):
    x = refine(p, d, first=True)
    y = refine(p, d, first=False)

    def cell_values(matrix, left, right):
        return np.einsum("abij,xia,yjb->xy", matrix.reshape(d, d, d, d), left, right, optimize=True)

    pair_values = cell_values(p, np.array(x), np.array(y)).real
    pairing = np.argmax(pair_values, axis=1)
    assert len(set(pairing)) == d
    assert np.array_equal(pair_values > 0.5, np.eye(d, dtype=bool)[:, np.argsort(pairing)])
    weights = (cell_values(h, np.array(x), np.array(y)[pairing]).real - b) / alpha
    off_diag = ~np.eye(d, dtype=bool)
    assert np.max(np.abs(weights[off_diag] - np.rint(weights[off_diag]))) < 0.125
    return np.rint(weights).astype(int)


def decode(k, n):
    anchor_count = 0
    anchor_type = {}
    for i, row in enumerate(k):
        partners = [j for j, a in enumerate(row) if i != j and abs(a) > 25]
        magnitudes = tuple(sorted(abs(row[j]) for j in partners))
        if magnitudes == (1000*n, 2000*n):
            anchor_type[i] = anchor_count
            anchor_count += 1
    assert anchor_count == n
    ports = {}
    for i, row in enumerate(k):
        linked = [j for j in anchor_type if 15 <= -row[j] <= 25]
        if not linked:
            continue
        assert len(linked) == 2 and row[linked[0]] == row[linked[1]]
        pair = tuple(sorted(anchor_type[j] for j in linked))
        ports[pair, -row[linked[0]]] = i
    return {
        pair for pair in combinations(range(n), 2)
        if k[ports[pair, 15], ports[pair, 19]] == 0
    }


def run_case(n, edges, rng):
    rho, b, alpha = template(n, edges)
    d = 3 * n * n
    u, v = (
        np.linalg.qr(rng.normal(size=(d, d)) + 1j*rng.normal(size=(d, d)))[0]
        for _ in range(2)
    )
    local = np.kron(u, v)
    h = local @ rho @ local.conj().T
    noise = rng.normal(size=h.shape) + 1j*rng.normal(size=h.shape)
    noise += noise.conj().T
    h += (alpha / 1000) * noise / np.linalg.norm(noise, "fro")
    eigenvalues, basis = np.linalg.eigh(h)
    high = basis[:, eigenvalues > b + 40*alpha]
    assert high.shape[1] == d
    decoded = decode(recover(high @ high.conj().T, h, b, alpha, d), n)
    assert any(
        decoded == {tuple(sorted((p[i], p[j]))) for i, j in edges}
        for p in permutations(range(n))
    )


if __name__ == "__main__":
    rng = np.random.default_rng(911)
    cases = ((2, set()), (2, {(0, 1)}), (3, {(0, 1), (1, 2)}))
    for n, edges in cases:
        run_case(n, edges, rng)
    print("3 independently scrambled graphs recovered with added Hermitian noise.")