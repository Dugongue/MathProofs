"""Construct generators for the unmarked subgroup reduction in Groups.md.

F_{3^e} elements are integers whose base-three digits are polynomial-basis
coefficients. Supply the low-to-high coefficients of the chosen irreducible
monic modulus, including its leading 1. The caller supplies the field model.
The cubic is a dictionary {(i,j,k): coefficient} with 0 <= i <= j <= k < n.
The public entry point is subgroup_generators(field, n, cubic).
"""
from itertools import permutations


class Field:
    def __init__(self, modulus):
        self.modulus = tuple(modulus)
        if len(modulus) < 2 or modulus[-1] != 1 or any(x not in (0, 1, 2) for x in modulus):
            raise ValueError("Expected a monic irreducible ternary polynomial.")
        self.e = len(modulus)-1
        self.q = 3**self.e

    def digits(self, a):
        result = []
        for _ in range(self.e):
            a, digit = divmod(a, 3)
            result.append(digit)
        return result

    def pack(self, coeffs):
        a = 0
        for x in reversed(coeffs):
            a = 3*a + x % 3
        return a

    def add(self, a, b):
        if self.e == 1:
            return (a+b) % 3
        return self.pack([x+y for x, y in zip(self.digits(a), self.digits(b))])

    def mul(self, a, b):
        if self.e == 1:
            return a*b % 3
        if not a or not b:
            return 0
        A, B = self.digits(a), self.digits(b)
        c = [0]*(2*self.e-1)
        for i, x in enumerate(A):
            for j, y in enumerate(B):
                c[i+j] += x*y
        for i in reversed(range(self.e, len(c))):
            for j, z in enumerate(self.modulus[:-1]):
                c[i-self.e+j] -= c[i]*z
        return self.pack(c[:self.e])

    def power(self, a, exponent):
        result = 1
        while exponent:
            if exponent % 2:
                result = self.mul(result, a)
            a = self.mul(a, a)
            exponent //= 2
        return result

    def total(self, terms):
        s = 0
        for x in terms:
            s = self.add(s, x)
        return s


def identity(d):
    return [[int(i == j) for j in range(d)] for i in range(d)]


def evaluate(k, cubic, x):
    return k.total(k.mul(a, k.mul(x[i], k.mul(x[j], x[t])))
                   for (i, j, t), a in cubic.items())


def translation(k, n, cubic, x):
    # H[i][j] = P_f(e_i,e_j,x).
    H = [[0]*n for _ in range(n)]
    for triple, a in cubic.items():
        kinds = len(set(triple))
        if kinds == 1:
            continue
        coefficient = k.mul(2, a) if kinds == 2 else a
        for i, j, t in set(permutations(triple)):
            H[i][j] = k.add(H[i][j], k.mul(coefficient, x[t]))
    half_square = [k.mul(2, k.total(k.mul(z, v) for z, v in zip(row, x))) for row in H]
    matrix = identity(2*n+2)
    matrix[-1][0] = evaluate(k, cubic, x)
    for i in range(n):
        matrix[1+i][0] = x[i]
        matrix[1+n+i][0] = half_square[i]
        matrix[-1][1+i] = half_square[i]
        matrix[-1][1+n+i] = x[i]
        for j in range(n):
            matrix[1+n+i][1+j] = H[i][j]
    return matrix


def restrict_to_three(k, matrix):
    size = len(matrix)*k.e
    result = [[0]*size for _ in range(size)]
    for i, row in enumerate(matrix):
        for j, a in enumerate(row):
            if a:
                for t in range(k.e):
                    for s, z in enumerate(k.digits(k.mul(a, 3**t))):
                        result[k.e*i+s][k.e*j+t] = z
    return result


def subgroup_generators(field, n, cubic):
    """Return matrices over the supplied field, in the encoding described above."""
    if n < 1 or any(len(t) != 3 or tuple(sorted(t)) != t or min(t) < 0 or max(t) >= n
                    or not 0 <= v < field.q for t, v in cubic.items()):
        raise ValueError("Invalid homogeneous cubic or number of variables.")
    descend = field.q == 3
    if n == 1 and descend:
        return [[[2, 0], [0, 1 if cubic.get((0, 0, 0), 0) else 2]]]
    k = Field((1, 0, 1)) if descend else field
    a = next(z for z in range(1, min(k.q, 23))
             if all(k.power(z, j) != 1 for j in range(1, 7)))
    generators = []
    for i in range(n):
        for t in range(k.e):
            x = [0]*n
            x[i] = 3**t
            generators.append(translation(k, n, cubic, x))
    size = 2*n+2
    grading = identity(size)
    for i, grade in enumerate([0]+[1]*n+[2]*n+[3]):
        grading[i][i] = k.power(a, grade)
    generators.append(grading)
    if descend:
        scalar = identity(size)
        for i in range(size):
            scalar[i][i] = a
        generators.append(scalar)
        generators = [restrict_to_three(k, m) for m in generators]
        frobenius = identity(2*size)
        # For i^2=-1, (x+iy)^3=x-iy.
        for j in range(size):
            frobenius[2*j+1][2*j+1] = 2
        generators.append(frobenius)
    return generators


def substitute(k, cubic, matrix):
    """Compute g(matrix*x) coefficientwise, including in the prime field."""
    out = {}
    for (i, j, t), v in cubic.items():
        for p, a in enumerate(matrix[i]):
            if not a:
                continue
            for r, b in enumerate(matrix[j]):
                if not b:
                    continue
                ab = k.mul(v, k.mul(a, b))
                for s, c in enumerate(matrix[t]):
                    if c:
                        key = tuple(sorted((p, r, s)))
                        out[key] = k.add(out.get(key, 0), k.mul(ab, c))
    return {key: v for key, v in out.items() if v}


def decode_conjugator(field, n, source, target, matrix):
    """Decode a supplied source-to-target group conjugator, checking formal equality."""
    source = {t: v for t, v in source.items() if v}
    target = {t: v for t, v in target.items() if v}
    if not source and not target:
        return identity(n)
    if field.q != 3:
        b, c = matrix[0][0], matrix[-1][-1]
        if not b or not c:
            raise ValueError("Expected invertible grade-zero and grade-three scalars.")
        inv_b = field.power(b, field.q-2)
        scale = field.mul(inv_b, field.power(field.mul(b, field.power(c, field.q-2)),
                                               field.q//3))
        h = [[field.mul(scale, matrix[1+i][1+j]) for j in range(n)] for i in range(n)]
    elif n == 1:
        h = [[source.get((0, 0, 0), 0)*target.get((0, 0, 0), 0) % 3]]
    else:
        # Multiplication by a translation can add higher-grade entries only.
        # On the base-field basis, a semilinear map gives the columns of its
        # linear part. Dividing by one entry removes the shared extension scalar.
        ext = Field((1, 0, 1))
        M = [[matrix[2*(i+1)][2*(j+1)] + 3*matrix[2*(i+1)+1][2*(j+1)]
              for j in range(n)] for i in range(n)]
        pivot = next((z for row in M for z in row if z), 0)
        if not pivot:
            raise ValueError("Zero degree-one map.")
        h = [[ext.mul(z, ext.power(pivot, 7)) for z in row] for row in M]
        if any(z >= 3 for row in h for z in row):
            raise ValueError("The normalized degree-one matrix does not descend.")
        transformed = substitute(field, target, h)
        if not source or source.keys() != transformed.keys():
            raise ValueError("Incompatible cubic coordinates.")
        key = next(iter(source))
        scale = source[key]*transformed[key] % 3
        h = [[z*scale % 3 for z in row] for row in h]
    if substitute(field, target, h) != source:
        raise ValueError("The recovered matrix fails formal cubic equality.")
    return h
