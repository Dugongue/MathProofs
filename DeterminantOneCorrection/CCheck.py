"""Independent finite controls for the volume quotient and counting reduction."""

from itertools import permutations, product
from math import gcd


def marks(columns, count):
    return [
        tuple(i for i, column in enumerate(columns) if (column >> j) & 1)
        for j in range(count)
    ]


def permutation_signs(columns, count):
    """Read every allowed permutation from the labeled ideals."""
    ideals = marks(columns, count)
    targets = [set(ideal) for ideal in ideals]
    signs = set()
    allowed = 0
    for permutation in permutations(range(len(columns))):
        images = [tuple(permutation[i] for i in ideal) for ideal in ideals]
        if any(set(image) != target for image, target in zip(images, targets, strict=True)):
            continue
        allowed += 1
        sign = 0
        for j, image in enumerate(images):
            inversions = sum(a > b for i, a in enumerate(image) for b in image[i+1:])
            sign |= (inversions % 2) << j
        signs.add(sign)
    return signs, allowed


def unit_image(columns, count, modulus):
    """Enumerate all unit actions by their multiplicative exponents."""
    ideals = marks(columns, count)
    return {
        tuple(sum(exponents[i] for i in ideal) % modulus for ideal in ideals)
        for exponents in product(range(modulus), repeat=len(columns))
    }


def span_binary(basis):
    space = {0}
    for row in basis:
        space |= {element ^ row for element in space}
    return space


def check_code(count, basis):
    columns = tuple(1 << j for j in range(count)) + basis + basis
    signatures, permutations_checked = permutation_signs(columns, count)
    assert signatures == span_binary(basis)
    assert len(unit_image(columns, count, 2)) == 2**count
    return permutations_checked


def check_norm_defect(divisor, modulus):
    count = divisor + 1
    full = (1 << count) - 1
    columns = tuple(full ^ (1 << j) for j in range(count))
    signatures, permutations_checked = permutation_signs(columns, count)
    assert signatures == {0}
    assert len(unit_image(columns, count, modulus)) * gcd(divisor, modulus) == modulus**count
    return permutations_checked


def incidence_syndrome(edges, edit, n):
    result = 0
    for bit, (i, j) in enumerate(edges):
        if (edit >> bit) & 1:
            result ^= (1 << i) | (1 << (n + j))
    return result


def matching_count(n, edges):
    return sum(
        all((row, col) in edges for row, col in enumerate(permutation))
        for permutation in permutations(range(n))
    )


def check_graphs():
    cases = 0
    edit_vectors = 0
    for n in range(1, 4):
        positions = tuple(product(range(n), repeat=2))
        target = (1 << (2 * n)) - 1
        for bits in range(1 << len(positions)):
            edges = tuple(edge for i, edge in enumerate(positions) if (bits >> i) & 1)
            edits = range(1 << len(edges))
            solutions = {e for e in edits if incidence_syndrome(edges, e, n) == target}
            kernel = {e for e in edits if incidence_syndrome(edges, e, n) == 0}
            if solutions:
                reference = min(solutions)
                assert solutions == {reference ^ codeword for codeword in kernel}
            repairs = sum(edit.bit_count() <= n for edit in solutions)
            assert repairs == matching_count(n, set(edges))
            edit_vectors += len(edits)
            cases += 1
    return cases, edit_vectors


def main():
    code_examples = (
        (1, ()), (1, (1,)), (2, (3,)), (3, (3, 5)), (4, (7, 13)),
        (4, (1, 14)), (4, (3, 12)),
    )
    valid_permutations = sum(check_code(count, basis) for count, basis in code_examples)
    norm_examples = ((2, 2), (2, 3), (2, 4), (3, 4), (3, 6), (4, 6))
    valid_permutations += sum(check_norm_defect(d, m) for d, m in norm_examples)
    cases, edits = check_graphs()
    print(f"{len(code_examples)} sign codes and {len(norm_examples)} norm defects checked.")
    print(f"{valid_permutations} allowed permutations across those controls.")
    print(f"{cases} bipartite graphs and {edits} edit vectors checked.")


if __name__ == "__main__":
    main()
