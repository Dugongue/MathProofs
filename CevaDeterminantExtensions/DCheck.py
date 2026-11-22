"""Check Segre diagonal rigidity and explicit modular span thresholds."""
from itertools import product


def binary_mul(a, b, polynomial, q):
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        if a & q:
            a ^= polynomial
        b >>= 1
    return value


def check_matrix_rigidity():
    def mul(a, b):
        return binary_mul(a, b, 4, 4)

    gl = []
    for a, b, c, d in product(range(4), repeat=4):
        if (mul(a, d) ^ mul(b, c)) & 1:
            gl.append((a, b, c, d))
    assert len(gl) == 96
    for G, J in product(gl, repeat=2):
        expected = G[1] == G[2] == J[1] == J[2] == 0
        diagonal = all(
            mul(G[2 * i + k], J[2 * j + l]) == 0
            for i, j, k, l in product(range(2), repeat=4)
            if (i, j) != (k, l))
        assert diagonal == expected
    return len(gl) ** 2


def rank(rows, degree):
    q = 1 << degree
    polynomial = {2: 7, 3: 11}[degree]

    def mul(a, b):
        return binary_mul(a, b, polynomial, q)

    pivots = {}
    for source in rows:
        row = list(source)
        for j in range(len(row)):
            if row[j] == 0:
                continue
            if j not in pivots:
                inverse = next(a for a in range(1, q) if mul(a, row[j]) == 1)
                pivots[j] = [mul(a, inverse) for a in row]
                break
            value = row[j]
            row = [a ^ mul(value, b) for a, b in zip(row, pivots[j], strict=True)]
    return len(pivots)


def check_thresholds():
    cases = 0
    for degree in (2, 3):
        q = 1 << degree
        polynomial = {2: 7, 3: 11}[degree]
        for n in range(1, q):
            for k in range(1, n + 1):
                matrix = []
                for alpha in range(n + 1):
                    powers = [1]
                    for _ in range(n - k):
                        powers.append(binary_mul(powers[-1], alpha, polynomial, q))
                    matrix.append(powers)
                for bits in product((0, 1), repeat=n):
                    no = [matrix[i] for i, yes in enumerate(bits) if not yes]
                    exposes = rank([*no, matrix[-1]], degree) > rank(no, degree)
                    assert exposes == (sum(bits) >= k)
                    cases += 1
    return cases


def check_wiring():
    import random
    random_source = random.Random(421)
    count = 0
    for order in (2, 3, 4, 6):
        for _ in range(12):
            variables = 3
            rows = [[random_source.randrange(order) for _ in range(variables)]
                    for _ in range(4)]
            gates = []
            outputs = []
            for row in rows:
                operands = [i + 1 for i, exponent in enumerate(row) for _ in range(exponent)]
                if not operands:
                    outputs.append(0)
                    continue
                current = 0
                for register in operands:
                    gates.append((current, register))
                    current = variables + len(gates)
                outputs.append(current)
            size = variables + len(gates) + 1
            tie = [frozenset(((i, 0), (0, i))) for i in range(1, size)]
            member = [frozenset(((i, 0), (0, 0))) for i in range(1, size)]
            wire = [frozenset(((i, j), (k, 0)))
                    for k, (i, j) in enumerate(gates, variables + 1)]
            assert all(len(pair) == 2 for pair in [*tie, *member, *wire])
            assert len(set([*tie, *member, *wire])) == len(tie) + len(member) + len(wire)
            for inputs in product(range(order), repeat=variables):
                registers = [0, *inputs]
                for i, j in gates:
                    registers.append((registers[i] + registers[j]) % order)
                for k, (i, j) in enumerate(gates, variables + 1):
                    assert (registers[i] + registers[j] - registers[k]) % order == 0
                actual = [registers[k] for k in outputs]
                expected = [sum(a * b for a, b in zip(row, inputs)) % order for row in rows]
                assert actual == expected
                count += 1
    return count


if __name__ == "__main__":
    print(f"{check_matrix_rigidity()} exact pairs of matrices over the binary dual numbers")
    print(f"{check_wiring()} group assignments with distinct supports and correct register values")
    print(f"{check_thresholds()} Vandermonde threshold cases over fields of sizes four and eight")
