"""Exact finite controls for Lazard word assembly and the marked ring."""

from collections import Counter
from itertools import product
from math import factorial
import random


class TruncatedAlgebra:
    def __init__(self, modulus, degree):
        self.modulus = modulus
        self.degree = degree
        self.one = {(): 1}

    def add(self, left, right, scale=1):
        result = dict(left)
        for word, coefficient in right.items():
            value = (result.get(word, 0) + scale * coefficient) % self.modulus
            if value:
                result[word] = value
            else:
                result.pop(word, None)
        return result

    def multiply(self, left, right):
        result = {}
        for (u, a), (v, b) in product(left.items(), right.items()):
            if len(u) + len(v) <= self.degree:
                uv = u + v
                result[uv] = (result.get(uv, 0) + a * b) % self.modulus
        return {word: coefficient for word, coefficient in result.items() if coefficient}

    def power(self, value, exponent):
        result = self.one
        while exponent:
            if exponent % 2:
                result = self.multiply(result, value)
            value = self.multiply(value, value)
            exponent //= 2
        return result

    def series(self, element, kind):
        power = self.one
        result = self.one if kind != "log" else {}
        for k in range(1, self.degree + 1):
            power = self.multiply(power, element)
            coefficient = {
                "exp": pow(factorial(k), -1, self.modulus),
                "log": (-1) ** (k - 1) * pow(k, -1, self.modulus),
                "inv": (-1) ** k,
            }[kind]
            result = self.add(result, power, coefficient)
        return result

    def inverse(self, unit):
        return self.series(self.add(unit, self.one, -1), "inv")

    def commutator(self, left, right):
        return self.multiply(
            self.multiply(self.multiply(left, right), self.inverse(left)),
            self.inverse(right),
        )

    def nested(self, word, generators):
        value = generators[word[0]]
        for letter in word[1:]:
            value = self.commutator(value, generators[letter])
        return value


def compile_words(algebra):
    x, y = {(0,): 1}, {(1,): 1}
    targets = ({(0,): 1, (1,): 1}, {(0, 1): 1, (1, 0): algebra.modulus - 1})
    generators = (algebra.series(x, "exp"), algebra.series(y, "exp"))
    programs = []
    for target in targets:
        value = algebra.one
        program = []
        for k in range(1, algebra.degree + 1):
            error = algebra.add(
                target, algebra.series(algebra.add(value, algebra.one, -1), "log"), -1
            )
            for word, coefficient in sorted(error.items()):
                if len(word) == k:
                    exponent = coefficient * pow(k, -1, algebra.modulus) % algebra.modulus
                    program.append((word, exponent))
                    value = algebra.multiply(
                        value, algebra.power(algebra.nested(word, generators), exponent)
                    )
        assert algebra.series(algebra.add(value, algebra.one, -1), "log") == target
        programs.append(program)
    return programs


def check_matrix_words(p, exponent, degree, rng):
    algebra = TruncatedAlgebra(p**exponent, degree)
    programs = compile_words(algebra)
    size = degree + 1
    modulus = algebra.modulus
    identity = tuple(tuple(int(i == j) for j in range(size)) for i in range(size))

    def add(a, b, scale=1):
        return tuple(tuple((a[i][j] + scale * b[i][j]) % modulus for j in range(size))
                     for i in range(size))

    def mul(a, b):
        return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(i, j + 1)) % modulus
                           for j in range(size)) for i in range(size))

    def power(a, k):
        value = identity
        while k:
            if k % 2:
                value = mul(value, a)
            a = mul(a, a)
            k //= 2
        return value

    def exp(n):
        value = identity
        for i in range(1, size):
            value = add(value, power(n, i), pow(factorial(i), -1, modulus))
        return value

    def sample():
        return tuple(tuple(rng.randrange(modulus) if i < j else 0 for j in range(size))
                     for i in range(size))

    def apply(program, generators):
        result = identity
        for word, exponent_value in program:
            value = generators[word[0]]
            for letter in word[1:]:
                other = generators[letter]
                value = mul(mul(mul(value, other), power(value, modulus - 1)),
                            power(other, modulus - 1))
            result = mul(result, power(value, exponent_value))
        return result

    for _ in range(24):
        x, y = sample(), sample()
        generators = exp(x), exp(y)
        assert apply(programs[0], generators) == exp(add(x, y))
        assert apply(programs[1], generators) == exp(add(mul(x, y), mul(y, x), -1))
    return 48


def check_corner_patterns():
    core = ("s0", "s1", "m0", "m1", "m2", "t0", "t1")
    l_corners = ("s0m0", "s0m1", "m0t0", "m2t0", "s0t0", "s0t1", "s1t0")
    r_corners = ("s0m2", "s1m0", "s1m2", "m0t1", "m1t0", "m1t1")
    core_edges = [(edge[:2], edge[2:]) for edge in l_corners + r_corners]
    for k in range(81):
        marks = [f"w{i}" for i in range(k)]
        edges = core_edges + [("h", v) for v in chain_core(core, marks)]
        edges.extend(("s0", mark) for mark in marks)
        edges.extend((mark, "t0") for mark in marks)
        edges.extend(zip(marks, marks[1:]))
        for j, v in enumerate(core, 1):
            edges.extend((v, f"leaf_{v}_{i}") for i in range(10 * j))
        edges.extend(("h", f"leaf_h_{i}") for i in range(2 * k + 100))
        indeg = Counter(v for _, v in edges)
        outdeg = Counter(u for u, _ in edges)
        assert outdeg["h"] > max(indeg.values())
        assert all(outdeg["h"] > n for u, n in outdeg.items() if u != "h")
        leaf_count = Counter(u for u, v in edges if outdeg[v] == 0)
        for j, v in enumerate(core, 1):
            assert [u for u, n in leaf_count.items() if n == 10 * j] == [v]
        assert {v for v in outdeg if v not in core and v != "h"} == set(marks)
    return 81


def chain_core(core, marks):
    yield from core
    yield from marks


def check_matrix_unit_annihilators():
    checked = 0
    for modulus in (2, 3, 4, 9):
        e01, e10 = (0, 1, 0, 0), (0, 0, 1, 0)

        def mul(a, b):
            return tuple(sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % modulus
                         for i in range(2) for j in range(2))

        zero = (0, 0, 0, 0)
        for a in product(range(modulus), repeat=4):
            assert (mul(a, e01) == zero and mul(a, e10) == zero) == (a == zero)
            assert (mul(e01, a) == zero and mul(e10, a) == zero) == (a == zero)
            checked += 2
    return checked


if __name__ == "__main__":
    rng = random.Random(11020)
    matrix_cases = sum(check_matrix_words(p, e, c, rng)
                       for p, e, c in ((3, 2, 2), (5, 2, 3), (5, 3, 4), (7, 2, 6)))
    print("Lazard word evaluations:", matrix_cases)
    print("Marked Peirce graphs:", check_corner_patterns())
    print("Matrix-unit annihilator cases:", check_matrix_unit_annihilators())
