"""Exact finite checks for the high-rank kernel and the common slice chains."""

from itertools import product
from random import Random


def row_basis(rows, p):
    pivots = {}
    for given in rows:
        row = {k: v % p for k, v in given.items() if v % p}
        while row:
            i = min(row)
            value = row[i]
            if i not in pivots:
                pivots[i] = {j: c * pow(value, -1, p) % p for j, c in row.items()}
                break
            eliminate(row, pivots[i], value, p)
    return pivots


def eliminate(row, pivot, factor, p):
    for j, coefficient in pivot.items():
        value = (row.get(j, 0) - factor * coefficient) % p
        if value:
            row[j] = value
        else:
            row.pop(j, None)


def reduce_mod_space(vector, pivots, p):
    row = {k: v % p for k, v in vector.items() if v % p}
    for i in sorted(pivots):
        if i in row:
            eliminate(row, pivots[i], row[i], p)
    return row


def anchor_matrix(x, y, z, full_rank, p):
    d = 4
    rows = [{i: x, i + d: y} for i in range(d)]
    rows[2][0] = z
    if full_rank:
        rows[3][1] = z
    return [{j: value % p for j, value in row.items() if value % p} for row in rows]


def quadratic_space(repetitions, full_rank, p):
    d = 4
    term_list = []
    for x, y, z in ((1, 0, 0), (0, 1, 0), (0, 0, 1)):
        matrix = anchor_matrix(x, y, z, full_rank, p)
        term_list.append({
            (copy * d + i, repetitions * d + copy * 2 * d + j): value
            for copy in range(repetitions)
            for i, row in enumerate(matrix)
            for j, value in row.items()
        })
    return row_basis(term_list, p)


def quadratic_product(left, right, p):
    result = {}
    for i, a in left.items():
        for j, b in right.items():
            key = (min(i, j), max(i, j))
            result[key] = (result.get(key, 0) + a * b) % p
    return {key: c for key, c in result.items() if c}


def vector_sum(first, second):
    result = first.copy()
    for index, value in second.items():
        result[index] = result.get(index, 0) + value
    return result


def multiply_augmentation(element, other, dim, monomials, h, p):
    """Product of two augmentation vectors over Z/(p^2)."""
    left = {i: a for i, a in element.items() if i < dim}
    right = {i: a for i, a in other.items() if i < dim}
    image = reduce_mod_space(quadratic_product(left, right, p), h, p)
    return {dim + monomials[j]: p * coefficient for j, coefficient in image.items()}


def main():
    h_direction, repetitions = 2, 3
    dim = 12 * repetitions
    monomials = {(i, j): index for index, (i, j) in enumerate(
        (i, j) for i in range(dim) for j in range(i, dim)
    )}
    rng = Random(391)
    anchors = restrictions = chains = 0
    for p in (2, 3):
        for full_rank in (False, True):
            labels = tuple(product(range(p), repeat=3))
            for x, y, z in labels:
                matrix = anchor_matrix(x, y, z, full_rank, p)
                rank = len(row_basis(matrix, p))
                assert (rank == 4) == bool(x or y)
                for xx, yy, zz in labels:
                    if (x * yy - y * xx) % p:
                        stacked = matrix + anchor_matrix(xx, yy, zz, full_rank, p)
                        assert len(row_basis(stacked, p)) == 8
                        anchors += 1
            h = quadratic_space(repetitions, full_rank, p)
            assert len(h) == 3
            for _ in range(8):
                u = {i: rng.randrange(p**2) for i in range(dim)}
                v = {i: rng.randrange(p**2) for i in range(dim)}
                u[0], v[0], v[1] = 1, 0, 1
                uv_rows = [quadratic_product(a, {i: 1}, p)
                           for a in (u, v) for i in range(dim)]
                assert len(row_basis(uv_rows, p)) == h_direction * dim - 1
                quotient_rows = [reduce_mod_space(row, h, p) for row in uv_rows]
                assert len(row_basis(quotient_rows, p)) == h_direction * dim - 1
                restrictions += 1

                w = {dim + monomials[dim - 2, dim - 1]: 1}
                u_plus_w = vector_sum(u, w)
                chain_vectors = [u_plus_w] + [{i: 1} for i in range(1, dim)]
                images = [multiply_augmentation(u, a, dim, monomials, h, p)
                          for a in chain_vectors]
                assert all(images)
                divided_images = [{i: c // p for i, c in image.items()} for image in images]
                assert len(row_basis(divided_images, p)) == dim
                assert all(not multiply_augmentation(u, image, dim, monomials, h, p)
                           for image in images)
                nonprimitive = {i: p * value for i, value in u.items()}
                assert all(not multiply_augmentation(nonprimitive, a, dim, monomials, h, p)
                           for a in chain_vectors)
                chains += 1
    print(f"{anchors} joint anchor checks, {restrictions} subpencil rank checks, "
          f"{chains} weighted chain checks")


if __name__ == "__main__":
    main()
