"""Exact finite controls for marked extension signatures and orbit weights."""

from collections import Counter
from itertools import permutations, product


def tuples(orders):
    return tuple(product(*(range(n) for n in orders)))


def scaled(multiple, element, orders):
    return tuple(multiple * a % n for a, n in zip(element, orders))


def added(left, right, orders):
    return tuple((a + b) % n for a, b, n in zip(left, right, orders))


def signature(kernel_orders, quotient_orders, carries):
    """Compute characters by repeatedly adding actual section lifts."""
    all_d = tuples(quotient_orders)
    records = []
    for j, power in enumerate(kernel_orders):
        values = []
        for d in all_d:
            if any(scaled(power, d, quotient_orders)):
                continue
            state = (0,) * len(d)
            value = 0
            for _ in range(power):
                sums = tuple(a + b for a, b in zip(state, d))
                value += sum(
                    carry[j] * (total // order)
                    for carry, total, order in zip(carries, sums, quotient_orders)
                )
                state = tuple(total % order for total, order in zip(sums, quotient_orders))
            assert not any(state)
            values.append(value % power)
        records.append(tuple(values))
    return tuple(records)


def check_abelian_classification():
    cases = [((4,), (2, 2)), ((2, 4), (2, 4)), ((3, 9), (3, 9))]
    counts = []
    for kernel_orders, quotient_orders in cases:
        forward, reverse = {}, {}
        all_e = tuples(kernel_orders)
        for carries in product(all_e, repeat=len(quotient_orders)):
            residues = tuple(
                tuple(c % min(u, v) for c, u in zip(carry, kernel_orders))
                for carry, v in zip(carries, quotient_orders)
            )
            characters = signature(kernel_orders, quotient_orders, carries)
            assert forward.setdefault(residues, characters) == characters
            assert reverse.setdefault(characters, residues) == residues
        counts.append((len(all_e) ** len(quotient_orders), len(forward)))
    assert counts == [(16, 4), (64, 32), (729, 243)]
    return counts


def check_abelian_orbit():
    orders = (4, 2, 2)
    quotient_orders = (2, 2, 2)
    group = tuples(orders)
    quotient = tuples(quotient_orders)
    zero = (0, 0, 0)

    def mark(element):
        return tuple(a % 2 for a in element)

    def linear(d, generator_images):
        value = zero
        for scalar, image in zip(d, generator_images):
            value = added(value, scaled(scalar, image, quotient_orders), quotient_orders)
        return value

    # Independently enumerate onto endomorphisms via every tuple of generator images.
    actual = Counter()
    for images in product(group, repeat=3):
        if any(any(scaled(o, g, orders)) for o, g in zip(orders, images)):
            continue
        full_image = set()
        for a in group:
            value = zero
            for scalar, gen in zip(a, images):
                value = added(value, scaled(scalar, gen, orders), orders)
            full_image.add(value)
        if len(full_image) == len(group):
            actual[tuple(mark(x) for x in images)] += 1

    # Independently enumerate quotient automorphisms and pull back the extension.
    orbit = Counter()
    surviving_counts = set()
    for images in product(quotient, repeat=3):
        if len({linear(d, images) for d in quotient}) != len(quotient):
            continue
        pulled_back = tuple(linear(d, images)[0] for d in quotient)
        orbit[pulled_back] += 1
        if pulled_back == tuple(d[0] for d in quotient):
            surviving_counts.add(actual[images])
        else:
            assert actual[images] == 0
    assert len(orbit) == 7
    assert set(orbit.values()) == {24}
    assert surviving_counts == {8}
    assert sum(actual.values()) == 24 * 8 == 192
    return len(orbit), 24, sum(actual.values())


def check_central_orbits():
    quotient = (0, 1, 2, 3)

    def cocycle(square_x, square_y):
        return tuple(
            (((x >> 1) & (y & 1))
             + square_x * (x & y & 1)
             + square_y * ((x & y) >> 1)) % 2
            for x in quotient for y in quotient
        )

    def canonical(weight):
        def changed(cochain):
            f = (0,) + cochain
            return tuple(
                (weight[4 * x + y] + f[x] + f[y] - f[x ^ y]) % 2
                for x in quotient for y in quotient
            )
        return min(changed(f) for f in product(range(2), repeat=3))

    def orbit(weight):
        result = Counter()
        for permutation in permutations(quotient[1:]):
            alpha = (0,) + permutation
            pullback = tuple(weight[4 * alpha[x] + alpha[y]] for x in quotient for y in quotient)
            result[canonical(pullback)] += 1
        return result

    def commutator(weight):
        return tuple(weight[4 * x + y] ^ weight[4 * y + x] for x in quotient for y in quotient)

    # These are Q8 and D8 by the presentation of two generators with central
    # commutator of order two, with respectively two and one nontrivial squares.
    quaternion, dihedral = cocycle(1, 1), cocycle(1, 0)
    assert commutator(quaternion) == commutator(dihedral)
    quaternion_orbit, dihedral_orbit = orbit(quaternion), orbit(dihedral)
    assert set(quaternion_orbit).isdisjoint(dihedral_orbit)
    assert (len(quaternion_orbit), set(quaternion_orbit.values())) == (1, {6})
    assert (len(dihedral_orbit), set(dihedral_orbit.values())) == (3, {2})

    # Independently enumerate epimorphisms by actual products of both
    # generator images and verify all products in the induced candidate map.
    def multiplication(weight, left, right):
        x, e = left
        y, f = right
        return x ^ y, e ^ f ^ weight[4 * x + y]

    def marked_epimorphisms(source, target):
        elements = tuple(product(quotient, range(2)))
        counts = Counter()
        for u, v in product(elements, repeat=2):
            if not u[0] or not v[0] or u[0] == v[0]:
                continue
            base = ((0, 0), u, v, multiplication(target, u, v))
            images = {element: (base[element[0]][0], base[element[0]][1] ^ element[1])
                      for element in elements}
            if all(images[multiplication(source, a, b)] == multiplication(target, images[a], images[b])
                   for a, b in product(elements, repeat=2)):
                counts[u[0], v[0]] += 1
        return counts

    q_to_q = marked_epimorphisms(quaternion, quaternion)
    d_to_d = marked_epimorphisms(dihedral, dihedral)
    assert len(q_to_q) == 6 and set(q_to_q.values()) == {4}
    assert len(d_to_d) == 2 and set(d_to_d.values()) == {4}
    assert not marked_epimorphisms(quaternion, dihedral)
    return len(quaternion_orbit), len(dihedral_orbit), sum(q_to_q.values()), sum(d_to_d.values())


if __name__ == "__main__":
    print("Abelian raw-extension counts and class counts:", check_abelian_classification())
    print("Abelian orbit size, multiplicity per state, total epimorphisms:", check_abelian_orbit())
    print("Quaternion/dihedral orbit sizes and respective automorphism counts:", check_central_orbits())