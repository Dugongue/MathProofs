"""Finite controls for central-shift transport and the original power records."""

from functools import cache
from itertools import product


class Module:
    def __init__(self, moduli):
        self.moduli = moduli
        self.elements = tuple(product(*(range(m) for m in moduli)))
        self.zero = self.elements[0]
        self.basis = tuple(tuple(int(i == j) for j in range(len(moduli)))
                           for i in range(len(moduli)))

    def add(self, x, y):
        return tuple((a + b) % m for a, b, m in zip(x, y, self.moduli))

    def scale(self, k, x):
        return tuple(k * a % m for a, m in zip(x, self.moduli))

    def eval(self, cols, x):
        return tuple(sum(a * c[j] for a, c in zip(x, cols)) % m
                     for j, m in enumerate(self.moduli))

    @cache
    def automorphisms(self):
        choices = tuple(tuple(x for x in self.elements if self.scale(order, x) == self.zero)
                        for order in self.moduli)
        output = []
        for cols in product(*choices):
            values = {x: self.eval(cols, x) for x in self.elements}
            if len(set(values.values())) == len(values):
                output.append(values)
        return output


class CentralGroup:
    def __init__(self, a, c, powers, brackets):
        self.a = a
        self.c = c
        self.powers = powers
        self.brackets = brackets
        self.one = (a.zero, c.zero)
        self.elements = tuple(product(a.elements, c.elements))

    def multiple_sum(self, terms):
        out = self.c.zero
        for multiple, value in terms:
            out = self.c.add(out, self.c.scale(multiple, value))
        return out

    def multiply(self, x, y):
        a, c = x
        b, d = y
        carries = (((x_i + y_i) // m, power)
                   for x_i, y_i, m, power in zip(a, b, self.a.moduli, self.powers))
        cross = ((a[j] * b[i], v) for (j, i), v in self.brackets.items())
        central = self.c.add(self.c.add(c, d),
                             self.c.add(self.multiple_sum(carries), self.multiple_sum(cross)))
        return self.a.add(a, b), central

    def beta(self, a, b):
        return self.multiple_sum((a[j] * b[i] - b[j] * a[i], v)
                                 for (j, i), v in self.brackets.items())

    def pow(self, x, order):
        value = self.one
        for _ in range(order):
            value = self.multiply(value, x)
        return value

    def shift(self, cols, g):
        a, c = g
        return a, self.c.add(c, self.c.eval(cols, a))

    def check_brackets(self, target, alpha, gamma):
        return all(gamma[self.beta(x, y)] == target.beta(alpha[x], alpha[y])
                   for x in self.a.basis for y in self.a.basis)

    def lift_choices(self, target, alpha, gamma):
        return [
            tuple((alpha[x], c) for c in target.c.elements
                  if target.pow((alpha[x], c), order) == (target.a.zero, gamma[power]))
            for x, power, order in zip(self.a.basis, self.powers, self.a.moduli)
        ]

    def lift_function(self, target, gamma, lifts):
        def f(g):
            a, c = g
            value = target.one
            for exponent, lift in zip(a, lifts):
                value = target.multiply(value, target.pow(lift, exponent))
            return target.multiply(value, (target.a.zero, gamma[c]))

        return f


def transport_cols(source, target, d, alpha, gamma):
    inverse = {y: x for x, y in alpha.items()}
    return tuple(gamma[source.c.eval(d, inverse[y])] for y in target.a.basis)


def nonsplit_mixed_controls():
    a, c = Module((2, 2, 4)), Module((2, 4))
    bracket = {(1, 0): (1, 0)}
    dihedral = CentralGroup(a, c, ((0, 0), (0, 0), (0, 0)), bracket)
    quaternion = CentralGroup(a, c, ((1, 0), (1, 0), (0, 0)), bracket)
    assert dihedral.beta(a.basis[1], a.basis[0]) == (1, 0)
    assert len(c.elements) > 2
    d = ((1, 0), (0, 0), (0, 1))
    admissible_pairs = contrasting_pairs = element_checks = 0
    for alpha, gamma in product(a.automorphisms(), c.automorphisms()):
        assert dihedral.check_brackets(dihedral, alpha, gamma) == dihedral.check_brackets(quaternion, alpha, gamma)
        if not dihedral.check_brackets(dihedral, alpha, gamma):
            continue
        assert not all(dihedral.lift_choices(quaternion, alpha, gamma))
        contrasting_pairs += 1
        choices = dihedral.lift_choices(dihedral, alpha, gamma)
        if not all(choices):
            continue
        admissible_pairs += 1
        for candidate, order in zip(choices, a.moduli):
            assert len(candidate) == sum(c.scale(order, z) == c.zero for z in c.elements)
        f = dihedral.lift_function(dihedral, gamma, tuple(v[0] for v in choices))
        transported = transport_cols(dihedral, dihedral, d, alpha, gamma)
        for g in dihedral.elements:
            assert f(dihedral.shift(d, g)) == dihedral.shift(transported, f(g))
            element_checks += 1
        sample = tuple((x, c.zero) for x in a.basis) + tuple((a.zero, y) for y in c.basis)
        for x, y in product(sample, repeat=2):
            assert f(dihedral.multiply(x, y)) == dihedral.multiply(f(x), f(y))
    assert contrasting_pairs > admissible_pairs > 0
    return contrasting_pairs, admissible_pairs, element_checks


def normalizer_control():
    a, c = Module((2, 2)), Module((2, 2))
    g = CentralGroup(a, c, (c.zero, c.zero), {})
    line = ((0, 0), (1, 0))
    shifts = set(product(line, repeat=2))
    normalizing_pairs = centralizing_pairs = 0
    induced = set()
    for alpha, gamma in product(a.automorphisms(), c.automorphisms()):
        action = {d: transport_cols(g, g, d, alpha, gamma) for d in shifts}
        if set(action.values()) != shifts:
            continue
        normalizing_pairs += 1
        centralizing_pairs += int(all(d == e for d, e in action.items()))
        induced.add(tuple(action[d] for d in sorted(shifts)))
    lift_kernel = 4**2
    assert (normalizing_pairs * lift_kernel,
            centralizing_pairs * lift_kernel, len(induced)) == (192, 32, 6)
    return normalizing_pairs * lift_kernel, centralizing_pairs * lift_kernel, len(induced)


if __name__ == "__main__":
    contrasting, admissible, elements = nonsplit_mixed_controls()
    normalizer, centralizer, action = normalizer_control()
    print("Equal-bracket pairs ruled out by cross-extension powers:", contrasting)
    print("Admissible mixed-exponent pairs with exact lift fibers:", admissible)
    print("Equations intertwining actual central shifts:", elements)
    print("Normalizer, centralizer and image orders in the abelian control:",
          normalizer, centralizer, action)
