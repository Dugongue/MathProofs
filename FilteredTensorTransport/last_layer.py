"""Recognize the ternary last-layer algebras from dense raw tensor tables.
solve(source,target,signs) returns a triple of matrices or None on the class.
An endpoint outside the family raises ValueError.
"""
from itertools import product
import flag_transport as ft


def transpose(rows):
    return tuple(zip(*rows))


def vector(matrix,v):
    return tuple(sum(x*y for x,y in zip(row,v)) % 3 for row in matrix)


def scale(a,v):
    return tuple(a*x % 3 for x in v)


def add(u,v):
    return tuple((x+y) % 3 for x,y in zip(u,v))


def span(vectors,d):
    return list(ft.rref(vectors,d)[0])


def require(condition):
    if not condition:
        raise ValueError("Outside the last-layer family")


def model(t,Q):
    r = len(Q)
    d = t+1+2*r
    zero = (0,)*d
    e = ft.eye(d)
    def pair(i,j):
        if i>j:
            return pair(j,i)
        if i==0:
            return e[j]
        if j<=t:
            return e[i+j] if i+j<=t else zero
        if i==1 and j<=t+r:
            return e[j+r]
        if t<i<=j<=t+r:
            return scale(Q[i-t-1][j-t-1],e[t])
        return zero
    return transpose([pair(i,j) for i,j in product(range(d),repeat=2)])


def recover(table):
    d = len(table)
    require(d>=6 and all(len(row)==d*d for row in table))
    table = tuple(tuple(x % 3 for x in row) for row in table)
    def slice_at(i,left):
        return tuple(tuple(row[(i*d+j) if left else (j*d+i)] for j in range(d)) for row in table)
    def choose(left):
        for i in range(d):
            a = slice_at(i,left)
            if len(ft.rref(a,d)[1])==d:
                return i,ft.inv(a)
        raise ValueError("No invertible basis slice")
    i,Linv = choose(True)
    j,Rinv = choose(False)
    unity = tuple(row[i*d+j] for row in table)
    alg = ft.mul(table,ft.tensor((Rinv,Linv)))
    def times(u,v):
        return vector(alg,tuple(x*y % 3 for x in u for y in v))
    e = ft.eye(d)
    require(all(times(unity,z)==z==times(z,unity) for z in e))
    cube = lambda z: times(times(z,z),z)
    powers = e
    exponent = 1
    while exponent<d:
        powers = tuple(cube(z) for z in powers)
        exponent *= 3
    J = ft.kernel(transpose(powers))
    require(len(J)==d-1)
    levels = [e,J]
    while levels[-1]:
        next_space = span([times(x,y) for x in J for y in levels[-1]],d)
        require(len(next_space)<len(levels[-1]))
        levels.append(next_space)
    t = len(levels)-2
    require(t>=3 and t%2==1)
    r = len(J)-len(levels[2])-1
    require(r>=1 and d==t+1+2*r)
    fourth,pivots,_ = ft.rref(levels[4],d)
    def mod_fourth(v):
        for j,row in zip(pivots,fourth):
            v = add(v,scale(-v[j],row))
        return v
    x = next((z for z in J if any(mod_fourth(cube(z)))),None)
    require(x is not None)
    xx = times(x,x)
    coeff = ft.kernel(transpose([times(xx,z) for z in J]))
    chosen = []
    current = list(levels[2])
    for a in coeff:
        y = vector(transpose(J),a)
        if any(mod_fourth(cube(y))):
            continue
        extension = span(current+[y],d)
        if len(extension)>len(current):
            current = extension
            chosen.append(y)
    require(len(chosen)==r)
    powers = [unity]
    for _ in range(t):
        powers.append(times(x,powers[-1]))
    E = transpose(powers+chosen+[times(x,y) for y in chosen])
    require(len(ft.rref(E,d)[1])==d)
    Einv = ft.inv(E)
    Q = tuple(tuple(vector(Einv,times(y,z))[t] for z in chosen) for y in chosen)
    require(Q==transpose(Q))
    require(ft.mul(alg,ft.tensor((E,E)))==ft.mul(E,model(t,Q)))
    return t,Q,(ft.mul(Rinv,E),ft.mul(Linv,E),E)


def diagonal(q):
    """Return a congruence frame with canonical diagonal entries in F3."""
    n = len(q)
    form = lambda u,v: sum(x*y for x,y in zip(u,vector(q,v)))%3
    space = list(ft.eye(n))
    pos,neg,rad = [],[],[]
    while space:
        k = next((i for i,v in enumerate(space) if form(v,v)),None)
        if k is None:
            pair = next(((i,j) for i in range(len(space)) for j in range(i)
                         if form(space[i],space[j])),None)
            if pair is None:
                rad = space
                break
            k,j = pair
            space[k] = add(space[k],space[j])
        v = space.pop(k)
        a = form(v,v)
        (pos if a==1 else neg).append(v)
        space = [add(w,scale(-form(v,w)*a,v)) for w in space]
    while len(neg)>=2:
        v,w = neg.pop(),neg.pop()
        pos.extend((add(v,w),add(v,scale(-1,w))))
    return (len(pos),len(neg),len(rad)),transpose(pos+neg+rad)


def solve(source,target,signs=(1,1,1)):
    t,q,frames = recover(source)
    tau,h,other = recover(target)
    if t!=tau or len(q)!=len(h):
        return None
    hsig,hframe = diagonal(h)
    r = len(q)
    d = len(source)
    for a in (1,2):
        sig,qframe = diagonal(tuple(scale(pow(a,t,3),row) for row in q))
        if sig != hsig:
            continue
        b = ft.mul(hframe,ft.inv(qframe))
        phi = [[0]*d for _ in range(d)]
        for i in range(t+1):
            phi[i][i] = pow(a,i,3)
        for i,j in product(range(r),repeat=2):
            phi[t+1+i][t+1+j] = b[i][j]
            phi[t+1+r+i][t+1+r+j] = a*b[i][j]%3
        maps = tuple(ft.mul(frame,ft.mul(phi,ft.inv(old))) for frame,old in zip(other,frames))
        if tuple(ft.rref(z,d)[2] for z in maps)!=tuple(signs):
            continue
        assert ft.mul(maps[2],source)==ft.mul(target,ft.tensor(maps[:2]))
        return maps
    return None
