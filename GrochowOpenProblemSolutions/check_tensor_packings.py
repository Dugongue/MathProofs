from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, prod


def affine_plane_packing():
    vertices = range(8)
    blocks = [block for block in combinations(vertices, 4)
              if block[0] ^ block[1] ^ block[2] ^ block[3] == 0]
    increasing = Counter(edge for block in blocks for edge in combinations(block, 3))
    bundled = Counter(edge for block in blocks for edge in permutations(block, 3))
    assert increasing == Counter(combinations(vertices, 3))
    assert bundled == Counter(permutations(vertices, 3))
    print(f"Complete triple packing: {len(blocks)} blocks, {len(increasing)} triples, {len(bundled)} orientations")


def composite_modulus_packing():
    modulus = 25
    order = 3
    parts = range(5)
    motif = [(3, 1, 0), (0, 1, 2), (4, 3, 1), (3, 1, 0)]
    counts = [Counter() for _ in motif]
    for coefficients in product(range(modulus), repeat=order):
        values = [sum(coefficient * point**degree
                      for degree, coefficient in enumerate(coefficients)) % modulus
                  for point in parts]
        for edge, count in zip(motif, counts):
            count[tuple(values[point] for point in edge)] += 1
    expected = Counter(product(range(modulus), repeat=order))
    assert all(count == expected for count in counts)
    print(f"Composite modulus: {modulus**order} blocks covering each cell triple exactly once per labeled edge")


def combine_at_vertices(edge_bits, edges):
    grouped = [[] for _ in range(4)]
    for bits, edge in zip(edge_bits, edges):
        for bit, vertex in zip(bits, edge):
            grouped[vertex].append(bit)
    return tuple(tuple(bits) for bits in grouped)


def synchronous_interpolation():
    edges = [(0, 1, 2), (1, 2, 3), (0, 2, 3)]
    basis = list(product(range(2), repeat=3))
    w = [bits for bits in basis if sum(bits) == 1]
    evaluations = list(range(1, 6))
    weights = {z: prod(Fraction(-w, z - w) for w in evaluations if w != z)
               for z in evaluations}

    actual = Counter()
    for z, weight in weights.items():
        for first, second, leftover in product(basis, basis, w):
            coeff_first = z ** sum(first) - int(sum(first) == 0)
            coeff_second = z ** sum(second) - int(sum(second) == 0)
            grouped = combine_at_vertices((first, second, leftover), edges)
            actual[grouped] += weight * Fraction(coeff_first * coeff_second, z**2)
    expected = Counter(combine_at_vertices(edge_bits, edges) for edge_bits in product(w, repeat=3))
    assert {key: value for key, value in actual.items() if value} == expected
    print(f"Synchronous interpolation: {len(evaluations)} evaluations, {sum(expected.values())} exact output terms")


affine_plane_packing()
composite_modulus_packing()
synchronous_interpolation()
