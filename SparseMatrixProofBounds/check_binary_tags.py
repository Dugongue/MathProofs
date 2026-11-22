"""Count reciprocal pairs of full Frobenius orbits via binary polynomials."""

def remainder(a, b):
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def irreducibles(d):
    return {
        f for f in range(1 << d, 2 << d)
        if all(remainder(f, g) for j in range(1, d // 2 + 1)
               for g in range(1 << j, 2 << j))
    }


def reciprocal(f):
    return int(format(f, "b")[::-1], 2)


for d, expected in [(1, 3), (2, 48)]:
    full = irreducibles(5 * d)
    pairs = {(f, reciprocal(f)) for f in full if f < reciprocal(f)}
    assert all(g in full for _, g in pairs)
    assert len(pairs) == expected and len(pairs) >= len(irreducibles(d))
    print(f"GF(2), input degree {d}: {len(pairs)} eligible tag pairs")
