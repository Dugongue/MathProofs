"""Finite controls for a radical-grade norm calculation."""
from itertools import product
import json


IDENTITY = 1, 0, 0, 1
SWAP = 0, 1, 1, 0


def multiply(left, right, scalar_add, scalar_mul):
    return tuple(
        scalar_add(
            scalar_mul(left[2 * i], right[j]),
            scalar_mul(left[2 * i + 1], right[2 + j]),
        )
        for i in range(2)
        for j in range(2)
    )


def dot_product_ring(a, b):
    """F2[epsilon]/(epsilon**2), with bit 1 storing the epsilon coefficient."""
    return ((a & 1) * (b & 1)) ^ (2 * (((a >> 1) * (b & 1)) ^ ((a & 1) * (b >> 1))))


def is_unit(matrix):
    a, b, c, d = matrix
    return (a * d - b * c) & 1


def norm(matrix, diagonal, inverse_diagonal, scalar_add, scalar_mul):
    transpose = matrix[0], matrix[2], matrix[1], matrix[3]
    to_multiply = lambda a, b: multiply(a, b, scalar_add, scalar_mul)
    h = 1, 0, 0, diagonal
    h_inv = 1, 0, 0, inverse_diagonal
    return to_multiply(to_multiply(to_multiply(h_inv, transpose), h), matrix)


def dual_number_checks():
    from collections import Counter
    norms = Counter(
        norm(matrix, 3, 3, lambda a, b: a ^ b, dot_product_ring)
        for matrix in product(range(4), repeat=4)
        if is_unit(matrix)
    )
    assert sum(norms.values()) == 96
    assert norms[IDENTITY] == 8
    assert norms[3, 0, 0, 3] == 8
    assert norms[3, 0, 0, 1] == 0
    assert norm(SWAP, 3, 3, lambda a, b: a ^ b, dot_product_ring) == (3, 0, 0, 3)
    residue_unitary_norms = {
        tuple(((entry ^ identity_entry) >> 1) & 1 for entry, identity_entry in zip(a, IDENTITY))
        for a in norms
        if tuple(x & 1 for x in a) == IDENTITY
    }
    assert residue_unitary_norms == {(0, 0, 0, 0), (0, 1, 1, 0), (1, 0, 0, 1), (1, 1, 1, 1)}
    return {"units": 96, "unitary_order": 8, "yes_target_norm_count": 8, "no_target_norm_count": 0}


def ring_checks(precision):
    from collections import Counter
    high = 2**precision
    low = high // 2
    scalar_add = lambda a, b: (a + b) % high
    scalar_mul = lambda a, b: (a * b) % high
    matrices = product(range(high), repeat=4)
    norms = Counter(
        norm(matrix, 3 % high, pow(3, -1, high), scalar_add, scalar_mul)
        for matrix in matrices if is_unit(matrix)
    )
    choose_mod_low = lambda a: tuple(x % low for x in a)
    unitary_low = {a for a in product(range(low), repeat=4) if is_unit(a)
                   and norm(a, 3 % low, pow(3, -1, low),
                            lambda x, y: (x+y)%low, lambda x, y: (x*y)%low) == IDENTITY}
    defect_coordinates = lambda a: tuple((x-y) // low % 2 for x, y in zip(a, IDENTITY))
    diag = lambda a: (a[0], a[3])
    orbit = {
        diag(defect_coordinates(norm(a, 3, pow(3, -1, high), scalar_add, scalar_mul)))
        for a in unitary_low
    }
    for x, y, z in product(range(2), repeat=3):
        h = 1 + low*x, low*y, low*y, 1 + low*z
        assert (norms[h] > 0) == ((x,z) in orbit)
    assert norms[IDENTITY] == 8 * len(unitary_low) // len(orbit)
    assert all(choose_mod_low(a) == IDENTITY for a in norms if norms[a] > 0 and a == IDENTITY)
    return {"modulus": high, "units": sum(norms.values()), "residue_unitary_order": len(unitary_low),
            "unitary_order": norms[IDENTITY], "obstruction_orbit": sorted(orbit)}


if __name__ == "__main__":
    print(json.dumps({"dual_numbers": dual_number_checks(),
                      "two_power_rings": [ring_checks(t) for t in range(2, 5)]}, indent=2))
