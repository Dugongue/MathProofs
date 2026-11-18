"""Check the symmetric-quartic marker identities over the rationals."""

from collections import defaultdict
from fractions import Fraction
from itertools import product


def add_symmetrized(tensor, a, b, c, d, value):
    for i, j in ((a, b), (b, a)):
        for k, l in ((c, d), (d, c)):
            tensor[i, j, k, l] += value


def partial_trace(tensor):
    result = defaultdict(Fraction)
    for (a, b, c, d), value in tensor.items():
        if b == d:
            result[a, c] += value
    return {key: value for key, value in result.items() if value}


def check_packing(components, side):
    span = 1
    while span**4 < components:
        span += 1
    colors = list(range(4 * span))
    parts = [range(i * span, (i + 1) * span) for i in range(4)]
    labels = list(product(*parts))[:components]
    entries = list(product(range(side), repeat=4))
    tensor = defaultdict(Fraction)

    def coord(color, index):
        return color * side + index

    def data_value(component, index):
        return Fraction((component + 1) * (index + 2), index + 3)

    def colored_tuple(label, entry):
        return tuple(coord(color, index) for color, index in zip(label, entry))

    for component, label in enumerate(labels):
        for index, entry in enumerate(entries):
            add_symmetrized(tensor, *colored_tuple(label, entry), data_value(component, index))

    for color in colors:
        scale = Fraction(color + 1, 2 * (side + 1))
        for i, j in product(range(side), repeat=2):
            a, b = coord(color, i), coord(color, j)
            add_symmetrized(tensor, a, b, a, b, scale)

    spectators = {}
    for source, target in product(colors, repeat=2):
        if source == target:
            continue
        first, second = [c for c in colors if c not in (source, target)][:2]
        spectators[source, target] = first
        for extra, sign in ((first, 1), (second, -1)):
            for i, j in product(range(side), repeat=2):
                a, b, c = coord(target, i), coord(extra, j), coord(source, i)
                add_symmetrized(tensor, a, b, c, b, Fraction(sign, side))

    assert partial_trace(tensor) == {
        (coord(color, i), coord(color, i)): color + 1
        for color in colors for i in range(side)
    }
    for (source, target), extra in spectators.items():
        for i, j in product(range(side), repeat=2):
            assert sum(tensor[coord(target, i), coord(extra, l),
                              coord(source, j), coord(extra, l)]
                       for l in range(side)) == int(i == j)
    for component, label in enumerate(labels):
        for index, entry in enumerate(entries):
            assert tensor[colored_tuple(label, entry)] == data_value(component, index)


if __name__ == "__main__":
    for number, side in [(1, 1), (2, 2), (16, 2), (17, 2), (81, 3)]:
        check_packing(number, side)
    print("Exact partial traces, transfer readouts, and all data entries pass in five cases.")
