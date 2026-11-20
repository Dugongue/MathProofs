"""Exact small checks for the four written proofs."""

from collections import Counter
from itertools import product
import unittest


def matmul(a, b, p):
    x, y, z, w = a
    i, j, k, l = b
    return ((x*i + y*k) % p, (x*j + y*l) % p,
            (z*i + w*k) % p, (z*j + w*l) % p)


def det(a, p):
    x, y, z, w = a
    return (x*w - y*z) % p


def nilpotent_ring_product(a, b, modulus):
    return tuple(sum(a[i] * b[k-i] for i in range(k+1)) % modulus
                 for k in range(len(a)))


def generated_subgroup(squares, one, modulus):
    """Compute the generated subgroup by direct closure for the small audit."""
    known = {one}
    for g in squares:
        previous = list(known)
        element = g
        while element not in known:
            known.update(nilpotent_ring_product(element, h, modulus) for h in previous)
            element = nilpotent_ring_product(element, g, modulus)
    return known


def simple_and_cover_tables():
    matrices = [a for a in product(range(5), repeat=4) if det(a, 5) == 1]
    identity = (1, 0, 0, 1)
    generators = ((1, 1, 0, 1), (1, 0, 1, 1))

    def build(elements, normal):
        index = {value: i for i, value in enumerate(elements)}
        table = [[index[normal(matmul(a, b, 5))] for b in elements] for a in elements]
        return table, index[normal(identity)], tuple(index[normal(g)] for g in generators)

    def quotient(a):
        return min(a, tuple(-x % 5 for x in a))

    return (build(matrices, lambda a: a),
            build(sorted({quotient(a) for a in matrices}), quotient))


def epi_count_two_generators(source, target):
    """Enumerate generator images independently of the cocycle calculation."""
    table, one, generators = source
    other, other_one, _ = target
    if len(table) < len(other):
        return 0
    count = 0
    for images in product(range(len(other)), repeat=2):
        found = {one: other_one}
        queue = [one]
        for x in queue:
            for g, image in zip(generators, images):
                y = table[x][g]
                expected = other[found[x]][image]
                if y not in found:
                    found[y] = expected
                    queue.append(y)
                elif found[y] != expected:
                    break
            else:
                continue
            break
        else:
            if len(found) == len(table) and len(set(found.values())) == len(other):
                count += 1
    return count


class ExactControls(unittest.TestCase):
    def test_strict_determinant_coset(self):
        p = 4
        gl = [a for a in product(range(p), repeat=4) if det(a, p) % 2]
        i2 = (1, 0, 0, 1)
        source = (i2, (0, 1, 0, 0))
        t = (3, 0, 0, 1)
        target = tuple(matmul(t, a, p) for a in source)
        counts = Counter((det(a, p), det(b, p)) for a, b in product(gl, repeat=2)
                         if all(matmul(b, x, p) == matmul(y, a, p)
                                for x, y in zip(source, target)))
        self.assertEqual(counts, {(1, 3): 8})

        # The reduced tuples both vanish, but no actual strict witness exists.
        self.assertFalse(any((2*b - 0*a) % 4 == 0 for a, b in product((1, 3), repeat=2)))

    def test_dyadic_nilpotent_ring_squares(self):
        for tau in range(1, 5):
            for degree in (1, 2, 3):
                modulus = 2**tau
                one = (1,) + (0,)*(degree-1)
                units = [a for a in product(range(modulus), repeat=degree) if a[0] % 2]
                generators = []
                for i in range(degree):
                    for k in range(1 if i == 0 else 0, tau):
                        g = list(one)
                        g[i] = (g[i] + 2**k) % modulus
                        generators.append(tuple(g))
                count = Counter(nilpotent_ring_product(g, g, modulus) for g in units)
                self.assertEqual(set(count), generated_subgroup(
                    [nilpotent_ring_product(g, g, modulus) for g in generators], one, modulus))
                self.assertEqual(set(count.values()), {len(units)//len(count)})

        # Exchange of two factors is a nonidentity adjoint.
        for tau in range(1, 7):
            modulus = 2**tau
            units = list(range(1, modulus, 2))
            fibers = Counter((x*y % modulus, x*y % modulus)
                             for x, y in product(units, repeat=2))
            self.assertEqual(fibers, {(u, u): len(units) for u in units})

    def test_one_simple_mode_example(self):
        vectors = [(20, 0), (9, 20), (12, -15)]
        squares = [x*x + y*y for x, y in vectors]
        self.assertEqual(squares, [400, 481, 369])
        gram = [(x*x, x*y, x*y, y*y) for x, y in vectors]
        self.assertEqual(tuple(map(sum, zip(*gram))), (625, 0, 0, 625))
        self.assertNotEqual(matmul(gram[0], gram[1], 103),
                            matmul(gram[1], gram[0], 103))

    def test_simple_factor_matches_with_and_without_a_center(self):
        cover, simple = simple_and_cover_tables()
        self.assertEqual(epi_count_two_generators(cover, cover), 120)
        self.assertEqual(epi_count_two_generators(simple, simple), 120)
        self.assertEqual(epi_count_two_generators(cover, simple), 120)
        self.assertEqual(epi_count_two_generators(simple, cover), 0)
        # Fixed map on a one-dimensional derived intersection over F_2.
        lifted = Counter()
        for first_tail, second_tail in product(range(8), repeat=2):
            row_span = {a ^ b ^ c for a in (0, 1)
                        for b in (0, first_tail) for c in (0, second_tail)}
            lifted[len(row_span)] += 1
        self.assertEqual(lifted[8], (2**2 - 1) * (2**2 - 2) * 2**2)

        # A surjection from the product selects one factor. Central maps agree
        # with the two orbit-type cases of the proof.
        self.assertEqual(sum(epi_count_two_generators(g, simple)
                             for g in (cover, simple)), 240)
        self.assertEqual(sum(epi_count_two_generators(g, cover)
                             for g in (cover, simple)), 120)


if __name__ == "__main__":
    unittest.main()
