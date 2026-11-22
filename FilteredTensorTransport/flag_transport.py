"""Ternary transport for two based input flags and an onto output.

Rows of table give output coordinates; columns are input pairs (i,j) in
lexicographic order. Width lists specify invariant suffix flags in these
bases. On arbitrary supplied flags the result is the flag-preserving answer.
Return (P,Q,S), or None. Determinants are 1 or 2 in F_3.
"""
from collections import deque
from itertools import product


def eye(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def rref(rows, width, limit=None):
    rows = [list(map(lambda x: x % 3, row)) for row in rows]
    pivots = []
    det = 1
    for j in range(width if limit is None else limit):
        i = len(pivots)
        p = next((k for k in range(i, len(rows)) if rows[k][j]), None)
        if p is None:
            continue
        if p != i:
            rows[i], rows[p] = rows[p], rows[i]
            det = -det
        if rows[i][j] == 2:
            rows[i] = [(-x) % 3 for x in rows[i]]
            det = -det
        for k, row in enumerate(rows):
            if k != i and row[j]:
                t = row[j]
                rows[k] = [(a-t*b) % 3 for a, b in zip(row, rows[i])]
        pivots.append(j)
    return tuple(tuple(row) for row in rows[:len(pivots)]), pivots, det % 3


def inv(a):
    n = len(a)
    rows, pivots, _ = rref([r+i for r, i in zip(a, eye(n))], 2*n, n)
    if len(pivots) != n:
        raise ValueError("Singular matrix")
    return tuple(row[n:] for row in rows)


def mul(a,b):
    cols = tuple(zip(*b))
    return tuple(tuple(sum(x*y for x,y in zip(row,col)) % 3 for col in cols) for row in a)


def mm(g,h):
    return (mul(g[0],h[0]), mul(g[1],h[1]))


def inverse(g):
    return (inv(g[0]), inv(g[1]))


def tensor(g):
    a,b = g
    return tuple(tuple(x*y % 3 for x in row for y in line) for row in a for line in b)


def act(g, space):
    if not space:
        return ()
    rows = mul(space, tuple(zip(*tensor(g))))
    return rref(rows,len(rows[0]))[0]


def kernel(a):
    rows,pivots,_ = rref(a,len(a[0]))
    free = sorted(set(range(len(a[0])))-set(pivots))
    result = []
    for col in free:
        v = [0]*len(a[0])
        v[col] = 1
        for i,j in enumerate(pivots):
            v[j] = -rows[i][col] % 3
        result.append(tuple(v))
    return tuple(result)


def orbit(x, gens, one, action):
    reps = {x:one}
    queue = deque([x])
    while queue:
        u = queue.popleft()
        for s in gens:
            v = action(s,u)
            if v not in reps:
                reps[v] = mm(s,reps[u])
                queue.append(v)
    return reps


def schreier(reps, gens, action, one):
    inverses = {k:inverse(t) for k,t in reps.items()}
    for u,t in reps.items():
        for s in gens:
            residual = mm(inverses[action(s,u)],mm(s,t))
            if residual != one:
                yield residual


def column_action(point):
    side,col,end = point
    def action(g,v):
        return tuple(sum(a*b for a,b in zip(row[:end],v)) % 3 for row in g[side][:end])
    return tuple(int(i == col) for i in range(end)), action


def compress(generators, base, one):
    # Keep a small strong generating set using the successive truncated columns.
    strong = [[] for _ in base]
    def tables():
        return [orbit(x,[g for layer in strong[i:] for g in layer],one,action)
                for i,(x,action) in enumerate(base)]
    reps = tables()
    def insert(g,start):
        for i in range(start,len(base)):
            x,action = base[i]
            v = action(g,x)
            if v not in reps[i]:
                strong[i].append(g)
                return True
            g = mm(inverse(reps[i][v]),g)
            if g == one:
                return False
        assert g == one
        return False
    for g in generators:
        if insert(g,0):
            reps = tables()
    while True:
        changed = False
        for i,(_, action) in enumerate(base):
            gs = [g for layer in strong[i:] for g in layer]
            if any(insert(h,i+1) for h in schreier(reps[i],gs,action,one)):
                changed = True
                break
        if not changed:
            return [g for layer in strong for g in layer]
        reps = tables()


def parabolic(widths):
    blocks = [i for i,k in enumerate(widths) for _ in range(k)]
    n = len(blocks)
    for i,j in product(range(n),repeat=2):
        if blocks[i] >= blocks[j]:
            a = [list(row) for row in eye(n)]
            a[i][j] = 2 if i == j else 1
            yield tuple(map(tuple,a))


def solve(source,target,left,right,det_targets=(1,1,1)):
    n,v = sum(left),sum(right)
    N = n*v
    if not source or len(source) != len(target) or min((*left,*right),default=0) <= 0:
        raise ValueError("Expected positive dimensions and matching tables")
    if any(len(row) != N for row in (*source,*target)) or any(d not in (1,2) for d in det_targets):
        raise ValueError("Invalid table width or determinant target")
    source,target = [tuple(tuple(a % 3 for a in row) for row in table) for table in (source,target)]
    m = len(source)
    _,pivots,_ = rref(source,N)
    if len(pivots) != m or len(rref(target,N)[1]) != m:
        raise ValueError("Output must be spanned")
    select = lambda a: tuple(tuple(row[j] for j in pivots) for row in a)
    section = inv(select(source))
    def quotient(g,to):
        return mul(select(mul(to,tensor(g))),section)
    one = (eye(n),eye(v))
    g0 = one
    gens = [(s,one[1]) for s in parabolic(left)] + [(one[0],s) for s in parabolic(right)]
    base = []
    for side,widths in enumerate((left,right)):
        for col in range(sum(widths)):
            end = 0
            for w in widths:
                end += w
                base.append(column_action((side,col,end)))
    block = lambda widths: [i for i,w in enumerate(widths) for _ in range(w)]
    a,b = block(left),block(right)
    order = sorted(range(N),key=lambda j:(a[j//v],b[j%v]))
    labels = [(a[j//v],b[j%v]) for j in order]
    cuts = [j for j in range(N) if not j or labels[j] != labels[j-1]] + [N]
    units = eye(N)
    def layers(table):
        rows = [tuple(r[j] for j in order) for r in kernel(table)]
        rows,p,_ = rref(rows,N)
        undo = [order.index(j) for j in range(N)]
        return [[tuple(row[j] for j in undo) for row,k in zip(rows,p) if k>=cut] for cut in cuts]
    xs,ys = layers(source),layers(target)
    for i in reversed(range(len(cuts)-1)):
        if len(xs[i]) != len(ys[i]):
            return None
        for j in range(i+1,len(cuts)):
            tail = [units[t] for t in order[cuts[j]:]]
            x = rref(xs[i]+tail,N)[0]
            y = act(inverse(g0),rref(ys[i]+tail,N)[0])
            reps = orbit(x,gens,one,act)
            if y not in reps:
                return None
            g0 = mm(g0,reps[y])
            if len(reps)>1:
                gens = compress(schreier(reps,gens,act,one),base,one)
    def signs(g,to):
        h = quotient(g,to)
        return tuple(rref(t,len(t))[2] for t in (*g,h))
    origin = signs(g0,target)
    wanted = tuple(a*b % 3 for a,b in zip(origin,det_targets))
    found = {(1,1,1):one}
    for g in gens:
        sg = signs(g,source)
        for u,word in list(found.items()):
            found.setdefault(tuple(a*b % 3 for a,b in zip(u,sg)),mm(g,word))
    if wanted not in found:
        return None
    g = mm(g0,found[wanted])
    h = quotient(g,target)
    assert mul(h,source) == mul(target,tensor(g)) and signs(g,target) == tuple(det_targets)
    return (*g,h)



def intrinsic_frame(table,n,v,side):
    size = (n,v)[side]
    relations = kernel(table)
    equations = []
    for r in relations:
        for row in table:
            if side == 0:
                equations.append([sum(row[k*v+j]*r[i*v+j] for j in range(v)) % 3
                                  for k in range(n) for i in range(n)])
            else:
                equations.append([sum(row[i*v+k]*r[i*v+j] for i in range(n)) % 3
                                  for k in range(v) for j in range(v)])
    flat = kernel(equations) if equations else eye(size*size)
    alg = [tuple(tuple(f[i*size:(i+1)*size]) for i in range(size)) for f in flat]
    gram = [[sum(a[i][j]*b[j][i] for i in range(size) for j in range(size)) % 3
             for a in alg] for b in alg]
    # In a commutative matrix algebra, a common large Frobenius power
    # is linear and its kernel is exactly the nilradical.
    if all(mul(a,b) == mul(b,a) for i,a in enumerate(alg) for b in alg[i+1:]):
        powers = alg
        exponent = 1
        while exponent < size:
            powers = [mul(a,mul(a,a)) for a in powers]
            exponent *= 3
        equations = [[a[i][j] for a in powers] for i in range(size) for j in range(size)]
        coeffs = kernel(equations)
    else:
        coeffs = kernel(gram)
    ideal = [tuple(tuple(sum(c*a[i][j] for c,a in zip(coeff,alg)) % 3
                         for j in range(size)) for i in range(size)) for coeff in coeffs]
    levels = [eye(size)]
    while levels[-1]:
        space = levels[-1]
        images = [tuple(sum(x*y for x,y in zip(row,w)) % 3 for row in g)
                  for g in ideal for w in space]
        next_level = rref(images,size)[0]
        if len(next_level) == len(space):
            levels.append(())
            break
        levels.append(next_level)
    columns = []
    widths = []
    for space in reversed(levels[:-1]):
        new = []
        for w in space:
            if len(rref(columns+new+[w],size)[1]) > len(columns)+len(new):
                new.append(w)
        columns = new+columns
        widths.insert(0,len(new))
    return tuple(zip(*columns)),widths


def solve_raw(source,target,n,v,det_targets=(1,1,1),fiber_budget=None):
    """Recover idealizer flags from independent raw tables; return based matrices.

    A supplied fiber_budget limits the proven worst-case orbit bound.
    An exceeded bound raises ValueError; None denotes mathematical infeasibility.
    """
    if n<=0 or v<=0 or not source or len(source)!=len(target):
        raise ValueError("Expected matching positive dimensions")
    if any(len(row)!=n*v for row in (*source,*target)):
        raise ValueError("Wrong dense table size")
    if any(len(rref(table,n*v)[1])!=len(table) for table in (source,target)):
        raise ValueError("Output must be spanned")
    a,aw = intrinsic_frame(source,n,v,0)
    b,bw = intrinsic_frame(source,n,v,1)
    c,cw = intrinsic_frame(target,n,v,0)
    d,dw = intrinsic_frame(target,n,v,1)
    if (aw,bw)!=(cw,dw):
        return None
    if fiber_budget is not None and 3**((max(aw)*max(bw))**2)>fiber_budget:
        raise ValueError("Certified flag-orbit bound exceeds budget")
    det = lambda matrix: rref(matrix,len(matrix))[2]
    calibrated = (det_targets[0]*det(a)*det(c)%3, det_targets[1]*det(b)*det(d)%3, det_targets[2])
    result = solve(mul(source,tensor((a,b))),mul(target,tensor((c,d))),aw,bw,calibrated)
    if result is None:
        return None
    p,q,s = result
    p,q = mul(c,mul(p,inv(a))),mul(d,mul(q,inv(b)))
    assert mul(s,source)==mul(target,tensor((p,q))) and tuple(map(det,(p,q,s)))==tuple(det_targets)
    return p,q,s
