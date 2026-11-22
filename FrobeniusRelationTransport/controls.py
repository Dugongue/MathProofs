"""Dense ternary examples. With a repository checkout, run python controls.py.
An optional argument supplies the path to the repository's CycleCompiler.py.
"""
import importlib.util
import json
import sys
from itertools import combinations_with_replacement
from pathlib import Path

path = Path(sys.argv[1]) if len(sys.argv) > 1 else (
    Path(__file__).resolve().parents[1] / "LargeRelationEvenTI" / "CycleCompiler.py")
spec = importlib.util.spec_from_file_location("cycle", path)
cycle = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cycle)


def factors(k):
    result = []
    d = 2
    while d*d <= k:
        if k % d == 0:
            result.append(d)
            while k % d == 0:
                k //= d
        d += 1
    return result + ([k] if k > 1 else [])


class Field:
    def __init__(self, n):
        self.n = n
        self.basis = [tuple(int(i == j) for i in range(n)) for j in range(n)]
        self.one, x = self.basis[:2]
        order = 3**n-1
        primes = factors(order)
        # Search a short polynomial modulus whose residue x has full order.
        for t in range(2, 3**n, 3):
            self.mod = tuple(t//3**i % 3 for i in range(n))
            if self.power(x, order) == self.one and all(
                    self.power(x, order//q) != self.one for q in primes):
                return
        raise ArithmeticError("No primitive polynomial found")

    def mul(self, x, y):
        n = self.n
        v = [0]*(2*n-1)
        for i, a in enumerate(x):
            if a:
                for j, b in enumerate(y):
                    v[i+j] += a*b
        for j in range(2*n-2, n-1, -1):
            a = v[j] % 3
            if a:
                for i, b in enumerate(self.mod):
                    v[j-n+i] -= a*b
        return tuple(c % 3 for c in v[:n])

    def power(self, x, e):
        y = self.one
        while e:
            if e % 2:
                y = self.mul(x, y)
            x = self.mul(x, x)
            e //= 2
        return y


def determinant(matrix):
    _, pivots, det = cycle.reduce(matrix, len(matrix))
    assert len(pivots) == len(matrix)
    return det


def check(n):
    field = Field(n)
    basis = field.basis
    pairs = list(combinations_with_replacement(range(n), 2))
    idx = {pair: j for j, pair in enumerate(pairs)}
    ix = [[idx[tuple(sorted((i, j)))] for j in range(n)] for i in range(n)]
    slices = []
    for shift in range(n//2+1):
        if shift in (1, 3):
            continue
        twist = [field.power(e, 3**shift) for e in basis]
        columns = []
        for i, j in pairs:
            a = field.mul(basis[i], twist[j])
            b = field.mul(twist[i], basis[j])
            columns.append(a if shift == 0 else tuple((s+t) % 3 for s, t in zip(a, b)))
        slices.extend(zip(*columns))
    width = len(pairs)
    table, pivots, _ = cycle.reduce(slices, width)
    m = len(table)
    relations = cycle.kernel_basis(table, pivots, width)
    assert len(relations) == 2*n and m == n*(n-3)//2
    equations = []
    for relation in relations:
        gradient = [[0]*n for _ in range(n)]
        for a, (i, j) in zip(relation, pairs):
            gradient[i][j] += a
            gradient[j][i] += a
        for row in table:
            equations.append([sum(gradient[i][j]*row[ix[k][j]] for j in range(n)) % 3
                              for k in range(n) for i in range(n)])
    _, leading, _ = cycle.reduce(equations, n*n)
    assert n*n-len(leading) == n
    sym_equations = []
    for row in table:
        for i, j in pairs:
            if i != j:
                sym_equations.append([((b == j)*row[ix[i][a]] - (b == i)*row[ix[j][a]]) % 3
                                      for a in range(n) for b in range(n)])
    assert len(cycle.reduce(sym_equations, n*n)[1]) == n*n-1

    signatures = []
    for columns in ([field.mul(basis[1], e) for e in basis],
                    [field.power(e, 3) for e in basis]):
        g = list(zip(*columns))
        transformed = [cycle.apply_matrix(table, cycle.product_coordinates(columns[i], columns[j], pairs))
                       for i, j in pairs]
        h = list(zip(*(transformed[j] for j in pivots)))
        for j, col in enumerate(zip(*table)):
            assert cycle.apply_matrix(h, col) == transformed[j]
        signatures.append((determinant(g), determinant(h)))
    subgroup = {(1, 1)}
    for u, v in signatures:
        subgroup |= {(a*u % 3, b*v % 3) for a, b in subgroup}
    assert subgroup == {(1, 1), (2, 2)}
    reflected_sl = any(a == 1 and a*pow(lam, n, 3) % 3 == 1
                       and 2*b*pow(lam, m, 3) % 3 == 1
                       for a, b in subgroup for lam in (1, 2))
    assert reflected_sl == (m % 2 == 1)
    assert all((2*a*b) % 3 == 2 for a, b in subgroup)
    return dict(input_dimension=n, output_dimension=m, relation_dimension=len(relations),
                derivation_dimension=n*n-len(leading), symmetrizer_dimension=1,
                modulus_low_first=field.mod, generator_determinants=signatures,
                output_reflection_SL=reflected_sl,
                reflected_combined_signs=[-1])


def check_blocks():
    from itertools import product
    degrees = (10, 14, 18)
    edges = ((0, 1), (1, 2), (0, 2))
    counts = {}
    for target in product(range(2), repeat=3):
        local = [set((s, t) for s in range(degrees[i]) for t in range(degrees[j])
                     if (s+t) % 2 == bit) for (i, j), bit in zip(edges, target)]
        assert all(local)
        total = sum(all((phase[i], phase[j]) in group for (i, j), group in zip(edges, local))
                    for phase in product(*(range(d) for d in degrees)))
        assert total == (0 if sum(target) % 2 else 630)
        counts["".join(map(str, target))] = total

    # Compute trace coefficients from the actual edge lists, including multiplicities.
    r, p = 4, 11
    d = 4*r+6
    trace_values = []
    for s in range(1, r+1):
        edges_s = {tuple(sorted((i, (i+j) % d))) for i in range(d) for j in range(1, 2*s, 2)}
        counts_s = [sum(i in edge for edge in edges_s) % p for i in range(d)]
        assert set(counts_s) == {2*s}
        trace_values.append(counts_s[0])
    assert len(set(trace_values)) == r
    return dict(degrees=degrees, phase_counts=counts, trace_prime=p,
                repeated_degree=d, trace_values=trace_values)


if __name__ == "__main__":
    print(json.dumps(dict(dense=[check(n) for n in (10, 12)], blocks=check_blocks()), indent=2))
