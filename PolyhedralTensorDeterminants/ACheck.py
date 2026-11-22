"""Finite checks of the coordinate determinant and connectivity laws."""

from itertools import combinations, product
from math import gcd


def units(modulus):
    return tuple(x for x in range(1, modulus) if gcd(x, modulus) == 1)


def determinant(scales, weights, modulus):
    value = 1
    for x, weight in zip(scales, weights):
        value = value * pow(x, weight, modulus) % modulus
    return value


def direct_image(modulus, group, edges, failed, weights):
    vertices = len(weights)
    group = set(group)
    unit_list = units(modulus)
    inverses = {x: pow(x, -1, modulus) for x in unit_list}
    image = set()
    for x in product(unit_list, repeat=vertices):
        if any(x[v] != x[w] for v, w in failed):
            continue
        if any(x[v] * inverses[x[w]] % modulus not in group for v, w in edges):
            continue
        image.add(determinant(x, weights, modulus))
    return image


def components(vertices, failed):
    unseen = set(range(vertices))
    result = []
    while unseen:
        component = {unseen.pop()}
        changed = True
        while changed:
            changed = False
            for v, w in failed:
                if v in component and w in unseen:
                    unseen.remove(w)
                    component.add(w)
                    changed = True
                elif w in component and v in unseen:
                    unseen.remove(v)
                    component.add(v)
                    changed = True
        result.append(component)
    return result


def exponent(modulus, group):
    return next(
        k for k in range(1, len(group) + 1)
        if all(pow(x, k, modulus) == 1 for x in group)
    )


def expected_image(modulus, group, failed, weights):
    exp = exponent(modulus, group)
    for component in components(len(weights), failed):
        exp = gcd(exp, sum(weights[v] for v in component))
    return {pow(x, exp, modulus) for x in group}


def check_coordinate_images():
    cases = 0
    graphs = [
        (3, ((0, 1), (1, 2), (0, 2))),
        (4, ((0, 1), (1, 2), (2, 3), (0, 3))),
        (4, tuple(combinations(range(4), 2))),
    ]
    for modulus, group in [(9, (1, 4, 7)), (8, units(8)), (7, units(7))]:
        for n, edges in graphs:
            weight_vectors = [(1, -1) + (0,) * (n - 2),
                              (1, 1, -2) + (0,) * (n - 3)]
            for flags in product((False, True), repeat=len(edges)):
                failed = [edge for edge, flag in zip(edges, flags) if flag]
                for weights in weight_vectors:
                    actual = direct_image(modulus, group, edges, failed, weights)
                    assert actual == expected_image(modulus, group, failed, weights)
                    if n == 3 and modulus == 9 and weights == (1, 1, -2):
                        assert (4 in actual) == (len(failed) <= 1)
                    cases += 1
    print(f"{cases} direct diagonal-image cases checked over Z/7, Z/8, and Z/9.")


def check_ceva():
    modulus = 9
    group = (1, 4, 7)
    coordinate_ratios = {
        (x * pow(y, -1, modulus) % modulus,
         y * pow(z, -1, modulus) % modulus,
         z * pow(x, -1, modulus) % modulus)
        for x, y, z in product(group, repeat=3)
    }
    concurrent = {
        (a, b, c) for a, b, c in product(group, repeat=3)
        if a * b * c % modulus == 1
    }
    assert coordinate_ratios == concurrent
    print("Every triple of principal side units over Z/9 passed the Ceva relation check.")


if __name__ == "__main__":
    check_coordinate_images()
    check_ceva()
