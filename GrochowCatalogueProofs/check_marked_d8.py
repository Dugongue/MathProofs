from collections import Counter
from itertools import product

IDENTITY = 0, 0
Z = 2, 0
ELEMENTS = list(product(range(4), range(2)))

def mul(a,b):
    return (a[0] + (-1 if a[1] else 1) * b[0]) % 4, a[1] ^ b[1]

def inverse(a):
    return (a[0] if a[1] else -a[0]) % 4, a[1]

def commutator(a,b):
    return mul(mul(mul(a,b),inverse(a)),inverse(b))

def central_bit(a):
    assert a in (IDENTITY,Z)
    return int(a == Z)

def test_assignment_counts(m):
    involutions = [a for a in ELEMENTS if mul(a,a) == IDENTITY]
    tuples = [u for u in product(involutions, repeat=m)
              if all(mul(a,b) == mul(b,a) for a in u for b in u)]
    counts = Counter()
    for a,b in product(tuples, repeat=2):
        matrix = tuple(tuple(central_bit(commutator(ai,bj)) for bj in b) for ai in a)
        if matrix[0][0] != 1:
            continue
        if any(matrix[i][j] != matrix[j][i] for i in range(m) for j in range(m)):
            continue
        if any(matrix[i][i] != matrix[0][i] for i in range(1,m)):
            continue
        x = matrix[0]
        assert matrix == tuple(tuple(xi*xj for xj in x) for xi in x)
        counts[x] += 1
    expected = {(1,)+x: 2**(2*m+1) for x in product(range(2),repeat=m-1)}
    assert dict(counts) == expected, (m, counts)
    # Exhaust every homogeneous degree-two equation on this many coordinates,
    # comparing Boolean solution count with all permitted target assignments.
    monomials = [(i,j) for i in range(m) for j in range(i,m)]
    for select in product(range(2),repeat=len(monomials)):
        terms = [term for used,term in zip(select,monomials) if used]
        test = lambda x: sum(x[i]*x[j] for i,j in terms)%2 == 0
        assert sum(k for x,k in counts.items() if test(x)) == sum(
            test((1,)+assignment) for assignment in product(range(2),repeat=m-1)
        )*2**(2*m+1)
    print(f'm={m}: {len(counts)} Boolean choices, {sum(counts.values())} marked maps, '
          f'all {2**len(monomials)} equations match')

for m in range(1,5):
    test_assignment_counts(m)
