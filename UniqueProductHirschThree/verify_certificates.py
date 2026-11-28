"""Verify the six finite certificates for the Hirsch-length-three proof."""

from collections import defaultdict
from pathlib import Path


EXPECTED = {
    "cert_p2_p.txt": (2, 1, 1, 14, 16, 5),
    "cert_p2_m.txt": (2, 1, -1, 16, 15, 5),
    "cert_p3m1_p.txt": (3, 1, 1, 19, 22, 5),
    "cert_p3m1_m.txt": (3, 1, -1, 19, 23, 5),
    "cert_p3m2_p.txt": (3, 2, 1, 24, 16, 5),
    "cert_p3m2_m.txt": (3, 2, -1, 19, 20, 7),
}


def product(first, second, order, lift_power, commutator):
    p, q, s, i = first
    x, y, z, j = second
    for _ in range(i):
        if order == 2:
            x, y = -x, -y
        else:
            x, y, z = -y, x - y, z + commutator * (y * (y - 1) // 2 - x * y)
    carry, holonomy = divmod(i + j, order)
    return p + x, q + y, s + z + commutator * q * x + carry * lift_power, holonomy


def read_certificate(path, order, lift_power, sign):
    lines = iter(path.read_text(encoding="utf-8").splitlines())
    expected = [0, order, lift_power, 0, 0, 0, 0, 0, sign]
    assert list(map(int, next(lines).split())) == expected

    def read_side(label):
        tag, size = next(lines).split()
        assert tag == label and int(size) > 0
        rows = [tuple(map(int, next(lines).split())) for _ in range(int(size))]
        assert all(len(row) == 7 and 0 <= row[2] < order for row in rows)
        assert len({row[:3] for row in rows}) == len(rows)
        return rows

    first = read_side("A")
    second = read_side("B")
    assert next(lines, None) is None
    return first, second


def check(path, order, lift_power, sign):
    first, second = read_certificate(path, order, lift_power, sign)
    classes = defaultdict(list)
    for p, q, i, a, a_low, a_neg, a_neg_low in first:
        for x, y, j, b, b_low, b_neg, b_neg_low in second:
            u, v, constant, h = product((p, q, 0, i), (x, y, 0, j), order, lift_power, 0)
            _, _, value, _ = product((p, q, 0, i), (x, y, 0, j), order, lift_power, 1)
            slope = sign * (value - constant)
            classes[u, v, h].append(
                ((a + b + slope, a_low + b_low + constant),
                 (a_neg + b_neg - slope, a_neg_low + b_neg_low - constant))
            )

    spread = 0
    for pairs in classes.values():
        for side in (0, 1):
            scores = [pair[side] for pair in pairs]
            maximum = max(scores)
            assert scores.count(maximum) >= 2
            constants = [constant for _, constant in scores]
            spread = max(spread, max(constants) - min(constants))
    return len(first), len(second), spread + 1, len(classes)


if __name__ == "__main__":
    folder = Path(__file__).with_name("certificates")
    assert {p.name for p in folder.iterdir()} == set(EXPECTED)
    for file, (order, lift_power, sign, a_size, b_size, threshold) in EXPECTED.items():
        actual = check(folder / file, order, lift_power, sign)
        assert actual[:3] == (a_size, b_size, threshold), (file, actual)
        print(f"{file}: {actual[3]} product classes, two ties per class, threshold {threshold}")
