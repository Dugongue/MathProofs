"""Exact ternary sign profiles from bounded spaces of slice intertwiners."""
from itertools import product


def slice_profile(shape, source, target, budget, eliminate, matrices, kernel, flatten):
    axis = min(range(3), key=shape.__getitem__)
    other = [i for i in range(3) if i != axis]
    m = shape[axis]
    n, k = (shape[i] for i in other)
    if 3**(m*m) > budget:
        return None
    order = other + [axis]
    s, t = (flatten(shape, data, order) for data in (source,target))
    width = n*n + k*k

    def mixed(coeff):
        return [sum(c*y for c,y in zip(coeff,col))%3 for col in zip(*t)]

    def rank(row):
        return len(eliminate([row[j:j+k] for j in range(0,n*k,k)])[1])

    # Every row of g is nonzero. Reuse its mixed slice and rank across candidates.
    mixed_rows = {v:mixed(v) for v in product(range(3),repeat=m) if any(v)}
    target_rank = {v:rank(row) for v,row in mixed_rows.items()}
    source_ranks = [rank(row) for row in s]
    found = set()
    incomplete = False
    for g, gbit in matrices(m):
        keys = [tuple(v) for v in g]
        if any(target_rank[v] != r for v,r in zip(keys,source_ranks)):
            continue
        equations = []
        for src,v in zip(s,keys):
            dst = mixed_rows[v]
            for i in range(n):
                for j in range(k):
                    row = [0]*width
                    for a in range(n):
                        row[n*i+a] = src[a*k+j]
                    for b in range(k):
                        row[n*n + k*b+j] = -dst[i*k+b] % 3
                    equations.append(row)
        basis = kernel(eliminate(equations), width)
        if 3**len(basis) > budget:
            incomplete = True
            continue
        for coefficients in product(range(3),repeat=len(basis)):
            if not any(coefficients):
                continue
            v = [sum(c*y for c,y in zip(coefficients,col))%3 for col in zip(*basis)]
            left = [v[i*n:(i+1)*n] for i in range(n)]
            right = [v[n*n+j*k:n*n+(j+1)*k] for j in range(k)]
            _, pivots, left_bit = eliminate(left)
            if len(pivots) != n:
                continue
            _, pivots, right_bit = eliminate(right)
            if len(pivots) == k:
                bits = [gbit]*3
                bits[other[0]], bits[other[1]] = left_bit,right_bit
                found.add(tuple(bits))
        if len(found) == 8:
            return found
    return None if incomplete else found
