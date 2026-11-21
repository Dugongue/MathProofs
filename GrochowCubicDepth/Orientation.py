"""Exact small controls for the integral orientation construction."""

from itertools import product
from math import factorial, prod


def permutation_sign(permutation):
    inversions = sum(
        left > right
        for index, left in enumerate(permutation)
        for right in permutation[index + 1 :]
    )
    return (-1) ** inversions


def carrier(blocks, radical):
    """One monomial on each disjoint, nonempty set of active variables."""
    arity = len(blocks[0][0])
    degree = sum(blocks[0][0])
    unit, top, marker, square = ("one",), ("top",), ("w",), ("square",)
    pieces = {i: [] for i in range(1, degree)}
    complement = {}
    top_coefficients = {}
    for exponent, coefficient in blocks:
        top_coefficients[exponent] = coefficient * prod(map(factorial, exponent))
        for key in product(*(range(value + 1) for value in exponent)):
            size = sum(key)
            if 0 < size < degree:
                pieces[size].append(("x", key))
                complement[key] = tuple(a - b for a, b in zip(exponent, key))

    half_rank = sum(len(pieces[i]) for i in range(1, (degree + 1) // 2))
    marker_count = 1 if (arity + degree * half_rank + degree * (degree + 1) // 2) % 2 else 2
    has_square = (arity + radical + degree + 2) % 2 == 1
    basis = [unit, top, marker]
    basis += [("radical", i) for i in range(radical)]
    basis += [("z", i) for i in range(1, degree)]
    for i in range(marker_count):
        basis += [("anchor", i), ("product", i)]
    basis += [("copy", i) for i in range(arity)]
    for piece in pieces.values():
        basis += piece
    if has_square:
        basis.append(square)

    oriented = dict.fromkeys(basis, 1)
    for i in range(1, (degree + 1) // 2):
        left = [key for _, key in pieces[i]]
        right = [key for _, key in pieces[degree - i]]
        permutation = [right.index(complement[key]) for key in left]
        sign = permutation_sign(permutation)
        for key in left:
            full = tuple(a + b for a, b in zip(key, complement[key]))
            sign *= 1 if top_coefficients[full] > 0 else -1
        oriented["x", right[0]] = sign

    def multiply(left, right):
        if left == unit or right == unit:
            return (right if left == unit else left), 1
        coefficient = 1
        if left[0] == right[0] == "x":
            key = tuple(a + b for a, b in zip(left[1], right[1]))
            if key in top_coefficients:
                output, coefficient = top, top_coefficients[key]
            else:
                output = ("x", key)
        elif left[0] == right[0] == "z":
            power = left[1] + right[1]
            output = top if power == degree else ("z", power)
        elif left[0] == "anchor" and right == ("z", 1):
            output = ("product", left[1])
        elif right[0] == "anchor" and left == ("z", 1):
            output = ("product", right[1])
        elif left == marker and right == marker:
            output = square
        elif left == marker and right[0] == "x" and sum(right[1]) == 1:
            output = ("copy", right[1].index(1))
        elif right == marker and left[0] == "x" and sum(left[1]) == 1:
            output = ("copy", left[1].index(1))
        else:
            return None, 0
        if output not in oriented:
            return None, 0
        return output, coefficient * oriented[left] * oriented[right] * oriented[output]

    return basis, oriented, multiply, marker_count, has_square


def signed_control(blocks, radical):
    arity = len(blocks[0][0])
    degree = sum(blocks[0][0])
    signs = (-1,) + (1,) * (arity - 1)
    target = [
        (key, value * prod(sign**power for sign, power in zip(signs, key)))
        for key, value in blocks
    ]
    basis, source_orient, source_mul, marker_count, has_square = carrier(blocks, radical)
    target_basis, target_orient, target_mul, flags, square = carrier(target, radical)
    assert (basis, marker_count, has_square) == (target_basis, flags, square)
    assert len(basis) % 2 == 0

    for a, beta, inertia in product((-1, 1), repeat=3):
        images = {}
        for key in basis:
            kind = key[0]
            image, scale = key, 1
            if kind == "x":
                scale = prod((a * sign) ** power for sign, power in zip(signs, key[1]))
            elif kind == "z":
                scale = a ** key[1]
            elif kind == "top":
                scale = a ** degree
            elif kind == "w":
                scale = beta
            elif kind == "copy":
                scale = beta * a * signs[key[1]]
            elif kind in ("anchor", "product"):
                image = (kind, marker_count - 1 - key[1])
                scale = (-1 if key[1] == 0 else 1) * (a if kind == "product" else 1)
            elif kind == "radical" and key[1] == 0:
                scale = inertia
            images[key] = (image, scale * source_orient[key] * target_orient[image])

        for left, right in product(basis, repeat=2):
            source_key, source_coefficient = source_mul(left, right)
            left_key, left_coefficient = images[left]
            right_key, right_coefficient = images[right]
            target_key, target_coefficient = target_mul(left_key, right_key)
            if source_key is None:
                assert target_key is None
            else:
                mapped_key, mapped_coefficient = images[source_key]
                assert mapped_key == target_key
                assert source_coefficient * mapped_coefficient == (
                    target_coefficient * left_coefficient * right_coefficient
                )
        permutation = [basis.index(images[key][0]) for key in basis]
        actual = permutation_sign(permutation) * prod(images[key][1] for key in basis)
        expected = -1 * (inertia if radical else 1)
        assert actual == expected

    return len(basis), marker_count, has_square


cubic = [((3, 0, 0), 2), ((0, 3, 0), 3), ((0, 0, 3), 5)]
quintic = [((3, 2, 0, 0, 0), 2), ((0, 0, 5, 0, 0), 3),
           ((0, 0, 0, 5, 0), 5), ((0, 0, 0, 0, 5), 7)]
assert signed_control(cubic, 0) == (18, 2, False)
assert signed_control(cubic, 1) == (20, 2, True)
assert signed_control(quintic, 0) == (36, 1, False)
print("Checked all products for 24 integral witnesses at ranks 18, 20, and 36.")
