"""Floating-point control for stable paired tensor-block recovery."""
from itertools import permutations

import numpy as np


def near_kernel_projector(matrix, lower_singular_bound):
    _, values, right = np.linalg.svd(matrix, full_matrices=False)
    selected = right[values < lower_singular_bound / 2]
    return selected.T @ selected


def recover(slices, k_bound, beta):
    _, d, _ = slices.shape
    dimension = 2 * d**2
    units = np.eye(dimension).reshape(dimension, 2, d, d)
    identity = np.eye(dimension)

    intertwiner = np.column_stack([
        (left @ slices - slices @ right).ravel()
        for left, right in units
    ])
    algebra = near_kernel_projector(intertwiner, beta / k_bound**4)
    generators = algebra.T.reshape(dimension, 2, d, d)
    commutator = np.column_stack([
        (g @ generators - generators @ g).ravel()
        for g in generators
    ])
    center = near_kernel_projector(np.concatenate((identity - algebra, commutator)), k_bound**-6)

    transpose = np.column_stack([u.transpose(0, 2, 1).ravel() for u in units])
    metric = center @ transpose @ center + identity - center
    metric_factor = np.linalg.cholesky(metric).T
    inverse_factor = np.linalg.inv(metric_factor)
    common_cells = [identity]
    cluster_gap = 1 / (20 * dimension * d**1.5 * k_bound**2)
    for z in center.T.reshape(dimension, 2, d, d):
        multiply = np.column_stack([(z @ u).ravel() for u in units])
        form = transpose @ multiply
        b = center @ (form + form.T) @ center / 2
        observable = inverse_factor.T @ b @ inverse_factor
        observed_values, vectors = np.linalg.eigh(observable)
        cut_indices = np.flatnonzero(np.diff(observed_values) > cluster_gap) + 1
        intervals = [v @ v.T for v in np.split(vectors, cut_indices, axis=1)]
        cells = (p @ q for p in common_cells for q in intervals)
        common_cells = [c for c in cells if np.trace(c) > 0.5]
    unit = np.tile(np.eye(d)[None, :, :], (2, 1, 1)).ravel()
    blocks = [
        (inverse_factor @ cell @ metric_factor @ unit).reshape(2, d, d)
        for cell in common_cells
    ]
    return [p for p in blocks if np.linalg.norm(p) > 0.5]


def control(multiplicities, noise_scale, rng):
    d = sum(multiplicities)
    profiles = np.array([[1, 0], [0, 1], [1, 1]])
    coefficients = np.repeat(profiles, multiplicities, axis=0)
    perturb = rng.standard_normal((2, d, d))
    bases = [np.eye(d) + p / (4 * np.linalg.norm(p, 2)) for p in perturb]
    left, right = bases
    left_inv, right_inv = [np.linalg.inv(x) for x in bases]
    exact = np.stack([left @ np.diag(c) @ right_inv for c in coefficients.T])
    assert all(np.linalg.matrix_rank(a) < d for a in exact)
    noise = rng.standard_normal(exact.shape)
    measured = exact + noise_scale * noise / np.linalg.norm(noise)
    recovered = recover(measured, k_bound=1.5, beta=0.6)
    assert len(recovered) == len(multiplicities)
    expected = []
    boundaries = np.cumsum([0, *multiplicities])
    for lo, hi in zip(boundaries, boundaries[1:]):
        index = np.zeros(d)
        index[lo:hi] = 1
        projection = np.diag(index)
        expected.append(np.stack((left @ projection @ left_inv, right @ projection @ right_inv)))
    best = min(permutations(recovered), key=lambda rows: sum(np.linalg.norm(x-y) for x,y in zip(rows,expected)))
    error = max(np.linalg.norm(x-y) for x,y in zip(best,expected))
    assert error < 1e-6
    print(f"multiplicities={multiplicities}, noise={noise_scale:.1e}, largest projector pair error={error:.2e}")


if __name__ == "__main__":
    rng = np.random.default_rng(7401)
    for blocks in [(1, 1, 1), (2, 1, 3)]:
        for scale in [0.0, 1e-9, 1e-7]:
            control(blocks, scale, rng)
