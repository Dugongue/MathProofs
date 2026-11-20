"""Finite controls for factoradic decoding and equivariant socle orbit counts."""

from collections import deque
from itertools import permutations, product
from math import factorial


def factor_image(rank, size, index):
    def position_at(j):
        return rank // factorial(j - 1) % j + 1

    position = position_at(index)
    for j in range(index + 1, size + 1):
        if position_at(j) <= position:
            position += 1
    return position


def check_factoradic():
    for size in range(1, 8):
        computed = {
            tuple(factor_image(rank, size, i) for i in range(1, size + 1))
            for rank in range(factorial(size))
        }
        assert computed == set(permutations(range(1, size + 1)))


def parity(p):
    return sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p))) % 2


def mul(p, q):
    return tuple(p[q[i]] for i in range(len(p)))


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def a5_automorphisms():
    identity = tuple(range(5))
    a5 = tuple(p for p in permutations(range(5)) if not parity(p))
    generator_pair = ((1, 2, 0, 3, 4), (1, 2, 3, 4, 0))
    automorphisms = []
    for image_pair in product(a5, repeat=2):
        images = {identity: identity}
        pending = deque([identity])
        valid = True
        while pending and valid:
            g = pending.popleft()
            for generator, image in zip(generator_pair, image_pair):
                new_g, new_image = mul(g, generator), mul(images[g], image)
                if new_g in images:
                    if images[new_g] != new_image:
                        valid = False
                        break
                else:
                    pending.append(new_g)
                    images[new_g] = new_image
        if valid and len(images) == len(a5) and len(set(images.values())) == len(a5):
            automorphisms.append(images)

    # Compare independently to ordinary conjugation by permutations.
    computed = {tuple(image[p] for p in a5) for image in automorphisms}
    conjugate = {
        tuple(mul(mul(c, p), inverse(c)) for p in a5)
        for c in permutations(range(5))
    }
    assert computed == conjugate
    return a5, automorphisms


def check_orbit_intertwiners():
    a5, automorphisms = a5_automorphisms()
    assert len(automorphisms) == 120
    nonidentity = a5[1:]
    flip = (1, 0, 2, 3, 4)

    def swap(element):
        factor, p = element
        return 1 - factor, p

    def twisted_swap(element):
        factor, p = element
        if factor == 0:
            return 1, p
        return 0, mul(mul(flip, p), flip)

    def intertwiner_count(source, target):
        count = 0
        for factor, psi in product(range(2), automorphisms):
            pending = deque(((0, p), (factor, psi[p])) for p in nonidentity)
            forward, backward = {}, {}
            valid = True
            while pending and valid:
                x, y = pending.popleft()
                if x in forward or y in backward:
                    valid = forward.get(x) == y and backward.get(y) == x
                else:
                    forward[x], backward[y] = y, x
                    pending.append((source(x), target(y)))
            if valid and len(forward) == len(backward) == 2 * len(nonidentity):
                count += 1
        return count

    counts = (
        intertwiner_count(swap, swap),
        intertwiner_count(swap, twisted_swap),
        intertwiner_count(twisted_swap, swap),
        intertwiner_count(twisted_swap, twisted_swap),
    )
    assert counts == (240, 0, 0, 24)
    return counts


if __name__ == "__main__":
    check_factoradic()
    print("Factoradic images agree with all permutations through degree 7.")
    print("A5 square swap/twisted-swap intertwiner counts:", check_orbit_intertwiners())
