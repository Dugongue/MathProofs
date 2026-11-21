"""Exact independent check of the GP-0091 mixed-torsion example."""
from collections import Counter
from itertools import product

PRIME = 5
TENSOR = {(0, 0, 0): 1, (1, 1, 0): 1, (1, 0, 1): 1, (0, 1, 1): 1}


def act(tensor, matrices):
    """Apply matrices on individual columns and reduce each torsion coordinate."""
    result = Counter()
    for (i, j, k), coefficient in tensor.items():
        for a, b, c in product(*(range(len(matrix)) for matrix in matrices)):
            result[a, b, c] += (
                coefficient * matrices[0][a][i] * matrices[1][b][j] * matrices[2][c][k]
            )
    return {key: (value % PRIME if key[1:] != (0, 0) else value)
            for key, value in result.items()
            if (value % PRIME if key[1:] != (0, 0) else value)}


def target(unit):
    return {key: unit if key[0] == 1 else value for key, value in TENSOR.items()}


def ordinary_targets():
    """Enumerate possible integral signs and all residual shears/units."""
    witnessed = Counter()
    targets = {tuple(sorted(target(unit).items())): unit for unit in range(1, PRIME)}
    checked = 0
    for a, d, e, f in product((-1, 1), repeat=4):
        if a * e * f != 1:
            continue
        for b, s, t in product(range(PRIME), repeat=3):
            for v, w in product(range(1, PRIME), repeat=2):
                matrices = (((a, b), (0, d)), ((e, 0), (s, v)), ((f, 0), (t, w)))
                actual = tuple(sorted(act(TENSOR, matrices).items()))
                checked += 1
                if actual in targets:
                    witnessed[targets[actual]] += 1
    return checked, witnessed


def main():
    checked, witnessed = ordinary_targets()
    assert checked == 16_000
    assert set(witnessed) == {1, 4}
    matrix = ((1, 0, 0), (0, 2, 5), (0, 5, 13))
    assert 2 * 13 - 5 * 5 == 1
    identity = ((1, 0), (0, 1))
    assert act(TENSOR, (matrix, identity, identity)) == target(2)
    print(f"Checked {checked} candidates. Ordinary units: {dict(witnessed)}. Stabilized unit: 2.")


if __name__ == "__main__":
    main()
