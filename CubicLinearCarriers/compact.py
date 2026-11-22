"""An ordinary multiplication tensor of side n+c+9 for a marked polar of rank c."""
from itertools import permutations
from fiber import Tensor, refinement_mark


def echelon(k, vectors):
    rows = {}
    for values in vectors:
        v = list(values)
        for j in sorted(rows):
            if v[j]:
                u = k.mul(2,v[j])
                v = [k.add(a,k.mul(u,b)) for a,b in zip(v,rows[j])]
        p = next((j for j,x in enumerate(v) if x), None)
        if p is not None:
            inv = k.power(v[p],k.q-2)
            rows[p] = [k.mul(inv,x) for x in v]
    return rows


def marked_algebra_tensor(k, n, cubic, mark):
    """Encode (polarization of cubic, mark) on the full input space."""
    P = {}
    for t, coefficient in cubic.items():
        kinds = len(set(t))
        if kinds == 1 or not coefficient:
            continue
        value = k.mul(2, coefficient) if kinds == 2 else coefficient
        for u in set(permutations(t)):
            P[u] = value

    covectors = (tuple(P.get((i,j,t),0) for t in range(n))
                 for i in range(n) for j in range(i,n))
    pivots = echelon(k, covectors)
    keys = sorted(pivots)
    c = len(keys)
    z, w, dual = n+1, n+2, n+3
    square_z, zw, top, right, m0, m1 = range(n+c+3, n+c+9)
    size = n+c+9
    table = {}
    for i in range(right):
        table[0,i,i] = table[i,0,i] = 1
    for i in range(n):
        for j in range(n):
            v = [P.get((i,j,t),0) for t in range(n)]
            for s,p in enumerate(keys):
                a = v[p]
                if a:
                    table[1+i,1+j,dual+s] = a
                    v = [k.add(x,k.mul(k.mul(2,a),y)) for x,y in zip(v,pivots[p])]
        for s,p in enumerate(keys):
            if pivots[p][i]:
                table[1+i,dual+s,top] = table[dual+s,1+i,top] = pivots[p][i]
        if mark[i]:
            table[1+i,m0,m1] = mark[i]
    table[z,z,square_z] = table[z,w,zw] = table[w,z,zw] = 1
    table[square_z,z,top] = table[z,square_z,top] = 1
    table[z,m0,m1] = 2
    table[right,right,right] = 1
    for m in (m0, m1):
        table[0,m,m] = table[m,right,m] = 1
    return Tensor(((size,), (size,), (size,)), lambda i,j,t: table.get((i,j,t), 0))


def compact_fiber_tensor(k, n, cubic):
    """None means this input failed the polar-preimage test."""
    mark = refinement_mark(k, n, cubic)
    if mark is None:
        return None
    return marked_algebra_tensor(k, n, cubic, mark)


def solve_columns(k, a, b):
    """Solve aX=b for an invertible matrix a, by simultaneous elimination."""
    n = len(a)
    aug = [list(row)+list(rhs) for row,rhs in zip(a,b)]
    for i in range(n):
        j = next((j for j in range(i,n) if aug[j][i]), None)
        if j is None:
            raise ValueError("Singular matrix in transporter normalization.")
        aug[i], aug[j] = aug[j], aug[i]
        inv = k.power(aug[i][i], k.q-2)
        aug[i] = [k.mul(inv, x) for x in aug[i]]
        for j in range(n):
            if j != i and aug[j][i]:
                factor = k.mul(2, aug[j][i])
                aug[j] = [k.add(x, k.mul(factor,y)) for x,y in zip(aug[j],aug[i])]
    return [r[n:] for r in aug]


def compact_decode(k, n, source, target, output_leg):
    """Given R with R(ab)=U(a)V(b) for the two compact algebras, decode h."""
    from groups import substitute
    tensor = compact_fiber_tensor(k, n, target)
    if tensor is None:
        raise ValueError("The target does not have a compact fiber carrier.")
    size = tensor.shape[0]
    right = size-3
    # R(1)=U(1)V(1), and 1=e_L+e_R in this algebra.
    unit_image = [k.add(row[0], row[right]) for row in output_leg]
    left_mult = [[k.total(k.mul(u, tensor.coefficient(i,j,t))
                          for i,u in enumerate(unit_image) if u)
                  for j in range(size)] for t in range(size)]
    phi = solve_columns(k, left_mult, output_leg)
    a = phi[n+1][n+1]
    if not a:
        raise ValueError("The cubic anchor has zero scale.")
    h = [[k.mul(k.power(a,k.q-2),phi[1+i][1+j]) for j in range(n)] for i in range(n)]
    source_mark = refinement_mark(k,n,source)
    target_mark = refinement_mark(k,n,target)
    if source_mark is None:
        raise ValueError("The source fails the rank test.")
    delta = [k.add(source_mark[j], k.mul(2,k.total(k.mul(target_mark[i],h[i][j])
             for i in range(n)))) for j in range(n)]
    if any(delta):
        # Find r in the target radical with target_mark(r)=1.
        equations = [[tensor.coefficient(1+i,n+3+s,size-4) for i in range(n)] + [0]
                     for s in range(size-n-9)] + [list(target_mark)+[1]]
        rows = echelon(k,equations)
        if n in rows:
            raise ValueError("The marked radical equations are inconsistent.")
        r = [0]*n
        for i in sorted(rows,reverse=True):
            correction = k.total(k.mul(rows[i][j],r[j]) for j in range(i+1,n))
            r[i] = k.add(rows[i][-1], k.mul(2,correction))
        h = [[k.add(x,k.mul(r[i],y)) for x,y in zip(row,delta)] for i,row in enumerate(h)]
    if substitute(k, target, h) != {t:x for t,x in source.items() if x}:
        raise ValueError("Decoded transformation fails the cubic identity.")
    return h
