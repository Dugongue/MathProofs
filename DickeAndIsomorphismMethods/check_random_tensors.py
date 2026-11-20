"""Exact finite checks for paired rank-one stabilizer conditions."""
from itertools import product
import random


def rank_signature(rows, prime, columns):
    rows = [[entry % prime for entry in row] for row in rows]
    rank = 0
    for column in range(columns):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        factor = pow(rows[rank][column], -1, prime)
        row = [(entry * factor) % prime for entry in rows[rank]]
        rows[rank] = row
        for i, other in enumerate(rows):
            if i != rank and other[column]:
                scale = other[column]
                rows[i] = [(a-scale*b) % prime for a,b in zip(other,row)]
        rank += 1
    return tuple(map(tuple, rows[:rank]))


def rank_one(n, prime):
    vectors = list(product(range(prime), repeat=n))
    result = {0: set(), 1: set()}
    for u, f in product(vectors[1:], repeat=2):
        trace = sum(x*y for x,y in zip(u,f)) % prime
        if trace in result:
            result[trace].add(tuple(tuple(x*y % prime for y in f) for x in u))
    return {k: sorted(v) for k,v in result.items()}


def constraints(u, z):
    n = len(u)
    rows = []
    for i, j in product(range(n), repeat=2):
        row = [0]*(n*n)
        for h in range(n):
            row[h*n+j] += u[i][h]
            row[i*n+h] -= z[h][j]
        rows.append(row)
    return rows


def verify_counts(prime):
    n = 3
    ranks = rank_one(n, prime)
    checked = set()
    counts = []
    modes = (0, 1) if prime > 2 else (0,)
    for trace in modes:
        count = len(checked)
        for u,z in product(ranks[trace], repeat=2):
            sig = rank_signature(constraints(u,z), prime,n*n)
            assert len(sig) == 2*n-2
            checked.add(sig)
        new = len(checked)-count
        expected = ((prime**n-1)*(prime**(n-1)-1)//(prime-1))**2//(prime-1) if trace==0 else (
            prime**(n-1)*(prime**n-1)//(prime-1))**2
        assert new == expected
        counts.append(new)
    return counts


def tensor_constraints(u, z, pair, prime):
    n = len(u)
    # (I+Z)^(-transpose) for a rank-one matrix.
    denominator = (1 + sum(z[i][i] for i in range(n))) % prime
    factor = pow(denominator, -1, prime)
    a = [[int(i == j)+u[i][j] for j in range(n)] for i in range(n)]
    b = [[int(i == j)-factor*z[j][i] for j in range(n)] for i in range(n)]
    basis = list(product(range(n), repeat=3))
    rows = []
    for x in basis:
        row = []
        for y in basis:
            entry = a[x[0]][y[0]]*b[x[pair]][y[pair]]*int(x[3-pair]==y[3-pair])
            row.append(entry-int(x==y))
        rows.append(row)
    return rows


def verify_overlap(prime):
    rng = random.Random(123)
    n = 3
    modes = rank_one(n, prime)
    traces = (0, 1) if prime > 2 else (0,)
    for _ in range(25):
        first = modes[rng.choice(traces)]
        second = modes[rng.choice(traces)]
        a,b = rng.choice(first),rng.choice(first)
        c,d = rng.choice(second),rng.choice(second)
        cells = tensor_constraints(a,b,1,prime)+tensor_constraints(c,d,2,prime)
        assert len(rank_signature(cells,prime,n**3)) >= 2*n*n-2*n+(n-2)*(n-1)

    # Distinct same-mode conditions with only one extra matrix constraint.
    # The common matrices all kill e_1, so the intersection is nonconcise.
    def unit(row, column):
        return tuple(tuple(int(i==row and j==column) for j in range(4))
                     for i in range(4))
    common = constraints(unit(0,1),unit(0,1))+constraints(unit(2,1),unit(0,3))
    signature = rank_signature(common,prime,16)
    assert len(signature) == 7
    for i in range(4):
        line_killer = [int(j==i*4) for j in range(16)]
        assert rank_signature(common+[line_killer],prime,16)==signature


if __name__=="__main__":
    for q in (2,3):
        print("q =", q, "distinct nilpotent and available semisimple events:", verify_counts(q))
        verify_overlap(q)
    print("50 cross-mode intersections and both nonconcise same-pair controls passed.")

