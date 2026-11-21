"""Finite probability checks for Topology.md. Uses only the Python standard library."""

from fractions import Fraction
from itertools import product
from math import log, log1p, sqrt, tanh


STATES = tuple(product(range(2), (-1, 1)))


def transition_matrix(forward, backward=None):
    if backward is None:
        backward = forward
    return [
        [
            (1 + (-1) ** (i + j) * (forward * u + backward * v)) / 4
            for j, v in STATES
        ]
        for i, u in STATES
    ]


def label_law(matrix, transitions, initial=None):
    if initial is None:
        initial = [Fraction(1, 4)] * 4
    paths = {
        (label,): [mass if i == label else Fraction(0)
                   for mass, (i, _) in zip(initial, STATES)]
        for label in range(2)
    }
    for _ in range(transitions):
        advanced = {}
        for path, masses in paths.items():
            for label in range(2):
                advanced[path + (label,)] = [
                    sum(mass * row[y] for mass, row in zip(masses, matrix))
                    if j == label else Fraction(0)
                    for y, (j, _) in enumerate(STATES)
                ]
        paths = advanced
    return {word: sum(masses) for word, masses in paths.items()}


def fitted_law(matrix, paths, memory):
    suffix = label_law(matrix, memory - 1)
    extended = label_law(matrix, memory)
    fitted = {}
    for word in paths:
        mass = suffix[word[:memory]]
        for t in range(memory, len(word)):
            mass *= extended[word[t - memory:t + 1]] / suffix[word[t - memory:t]]
        fitted[word] = mass
    assert sum(fitted.values()) == 1
    return fitted


def relative_entropy(actual, fitted):
    return sum(float(p) * log1p(float((p - fitted[word]) / fitted[word]))
               for word, p in actual.items() if p)


def main():
    horizon = 10
    for epsilon in (Fraction(1, 4), Fraction(1, 8), Fraction(1, 16)):
        matrix = transition_matrix(epsilon)
        assert all(sum(row) == 1 for row in matrix)
        assert all(matrix[x][y] == matrix[y][x] for x, y in product(range(4), repeat=2))
        triples = label_law(matrix, 2)
        assert all(
            p == (1 + epsilon**2 * (-1)**(i + k)) / 8
            for (i, _, k), p in triples.items()
        )
        actual = label_law(matrix, horizon)
        assert sum(actual.values()) == 1
        assert len(actual) == 2048

        e = float(epsilon)
        radical = sqrt(1 - 4 * e**2)
        contraction = (1 - radical) / (1 + radical)
        reverse_radius = log((1 + e) / (1 - e)) / (1 - contraction)
        for memory in (1, 2):
            fitted = fitted_law(matrix, actual, memory)
            divergence = relative_entropy(actual, fitted)
            denominator = 1 if memory == 1 else 1 - e
            residual = tanh(contraction**(memory - 1) * reverse_radius / 4)
            upper = (horizon - memory) * 4 * e**2 * residual**2 / denominator
            assert divergence <= upper + 1e-13
            if memory == 1:
                contrast = e**2
                lower = (horizon - 1) * (
                    (1 + contrast) * log1p(contrast)
                    + (1 - contrast) * log1p(-contrast)
                ) / 2
                assert divergence >= lower - 1e-13
            print(f"epsilon={epsilon}, memory={memory}, KL={divergence:.12g}, "
                  f"bound={upper:.12g}, paths={len(actual)}")

    epsilon = Fraction(1, 4)
    asymmetric = transition_matrix(epsilon, backward=0)
    assert all(sum(column) == 1 for column in zip(*asymmetric))
    assert set(label_law(asymmetric, 4).values()) == {Fraction(1, 32)}
    concentrated = label_law(asymmetric, 1, [0, 1, 0, 0])
    assert concentrated[(0, 0)] == (1 + epsilon) / 2
    assert concentrated[(0, 1)] == (1 - epsilon) / 2
    print("The backward-lumpable example is stationary-iid but has an initial bias.")

    forward = Fraction(1, 5)
    backward = Fraction(1, 7)
    mixed = transition_matrix(forward, backward)
    assert all(sum(row) == 1 for row in mixed)
    assert all(sum(column) == 1 for column in zip(*mixed))
    assert all(
        p == (1 + forward * backward * (-1)**(i + k)) / 8
        for (i, _, k), p in label_law(mixed, 2).items()
    )
    print("Unequal nonzero defects give the predicted product bias.")


if __name__ == "__main__":
    main()
