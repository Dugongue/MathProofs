"""Small exact checks of the bordered Hom rank and parameter-compression identities."""
from itertools import product


def rank(matrix, p):
    a = [row[:] for row in matrix]
    if not a:
        return 0
    pivot = 0
    for j in range(len(a[0])):
        i = next((i for i in range(pivot, len(a)) if a[i][j] % p), None)
        if i is None:
            continue
        a[pivot], a[i] = a[i], a[pivot]
        c = pow(a[pivot][j] % p, -1, p)
        a[pivot] = [c * e % p for e in a[pivot]]
        for i in range(len(a)):
            if i != pivot:
                c = a[i][j] % p
                a[i] = [(u - c*v) % p for u, v in zip(a[i], a[pivot])]
        pivot += 1
    return pivot


def pair_rank(s, matrices, p):
    # S has dimensions (1,1) and a nonzero two-arrow tuple, so its residue is the first node.
    a, b = len(matrices[0]), len(matrices[0][0])
    forward = []
    reverse = []
    for scalar, arrow in zip(s, matrices):
        for i in range(a):
            forward.append(arrow[i] + [-scalar * int(i == j) for j in range(a)])
        for j in range(b):
            reverse.append([scalar * int(j == i) for i in range(b)] + [-arrow[i][j] for i in range(a)])
    m = a + b
    bordered = [[int(i == j and i < b) for j in range(m)] + [row[i] for row in forward]
                for i in range(m)]
    bordered += [row[:] + [0]*len(forward) for row in reverse]
    return rank(bordered, p)-rank(forward, p)-rank(reverse, p)


def multiply(left, right, p):
    return [[sum(a*b for a, b in zip(row, column)) % p for column in zip(*right)] for row in left]


def rank_checks():
    tested = 0
    for p in (2, 3, 5):
        lines = [(1, a) for a in range(p)] + [(0, 1)]
        for first, second in product(lines, repeat=2):
            for left, right in [([[1, 1], [0, 1]], [[0, 1], [1, 1]]),
                                ([[1, 0], [1, 1]], [[1, 1], [1, 0]])]:
                matrices = [multiply(multiply(left, [[first[i], 0], [0, second[i]]], p), right, p)
                            for i in range(2)]
                for s in lines:
                    assert pair_rank(s, matrices, p) == int(s == first) + int(s == second)
                    tested += 1
        # One length-two Jordan pencil is indecomposable and has no simple line as a summand.
        for a in range(p):
            matrices = [[[1, 0], [0, 1]], [[a, 1], [0, a]]]
            for s in lines:
                assert pair_rank(s, matrices, p) == 0
                tested += 1
    return tested


def nilpotence_checks():
    # f=w1,w2 in the local Artin ring with w1^e=w2^e=0.
    # The E-fold product from the proof is zero even over small characteristic.
    from math import comb
    cases = 0
    for p in (2, 3, 5, 7):
        for e in range(1, 9):
            E = 2*(e-1) + 1
            for a, b in product(range(p), repeat=2):
                for j in range(E+1):
                    coefficient = comb(E, j)*pow(a, j, p)*pow(b, E-j, p) % p
                    assert not coefficient or j >= e or E-j >= e
                cases += 1
    return cases


if __name__ == "__main__":
    print("Bordered Hom multiplicity checks:", rank_checks())
    print("Nilpotent product checks:", nilpotence_checks())
