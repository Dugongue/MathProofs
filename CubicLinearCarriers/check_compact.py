"""Check ordinary algebra tensors, arbitrary-leg normalization and radical recovery."""
from functools import cache
from compact import compact_fiber_tensor, compact_decode, solve_columns
from groups import Field, identity, substitute
from check_groups import mm


def basis(n, i):
    return [int(j == i) for j in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def image(k, matrix, v):
    return [k.total(k.mul(a,b) for a,b in zip(row,v) if a and b) for row in matrix]


def operations(k,t):
    size = t.shape[0]
    table = {(i,j): [(v,a) for v in range(size) if (a:=t.coefficient(i,j,v))]
             for i in range(size) for j in range(size)}
    def product(x,y):
        result = [0]*size
        for i,a in enumerate(x):
            if a:
                for j,b in enumerate(y):
                    if b:
                        for v,s in table[i,j]:
                            result[v] = k.add(result[v],k.mul(s,k.mul(a,b)))
        return result
    return product


def check(k, n, f, g, phi):
    t, target = compact_fiber_tensor(k,n,f), compact_fiber_tensor(k,n,g)
    size = t.shape[0]
    assert t.shape == target.shape == (size,)*3
    src, dst = operations(k,t), operations(k,target)
    vs = [basis(size,i) for i in range(size)]
    unit = basis(size,0)
    unit[size-3] = 1
    u, v = unit[:], unit[:]
    u[n+1] = u[size-2] = v[n+2] = 1
    U = [dst(u,image(k,phi,x)) for x in vs]
    V = [dst(image(k,phi,x),v) for x in vs]
    R = transpose([dst(U[i],v) for i in range(size)])
    for i in range(size):
        assert src(unit,vs[i]) == src(vs[i],unit) == vs[i]
        for j in range(size):
            assert dst(U[i],V[j]) == image(k,R,src(vs[i],vs[j]))
    h = compact_decode(k,n,f,g,R)
    assert substitute(k,g,h) == f
    return size**2, h


if __name__ == "__main__":
    total = 0
    for k in [Field((0,1)), Field((1,0,1))]:
        k.mul, k.add = cache(k.mul), cache(k.add)
        n, m = 8, 4
        g = {(m,m,m):1}
        for i in range(m):
            g[i,i,m+i] = 1
            g[tuple(sorted((i,(i+1)%m,m+i)))] = 1
        h = identity(n)
        for i in range(n):
            for j in range(n):
                h[i][j] = k.add(h[i][j],k.mul(2 if k.q==3 else 3,h[(i+1)%n][j]))
        f = substitute(k,g,h)
        S, T = compact_fiber_tensor(k,n,f), compact_fiber_tensor(k,n,g)
        size = S.shape[0]
        assert size == 2*n+9
        # Pairings with degree one specify the map on all concise degree-two covectors.
        cf = [[S.coefficient(1+i,n+3+j,size-4) for j in range(n)] for i in range(n)]
        cg = [[T.coefficient(1+i,n+3+j,size-4) for j in range(n)] for i in range(n)]
        dual = solve_columns(k,mm(k,transpose(h),cg),cf)
        phi = identity(size)
        for i in range(n):
            for j in range(n):
                phi[1+i][1+j] = h[i][j]
                phi[n+3+i][n+3+j] = dual[i][j]
        count, decoded = check(k,n,f,g,phi)
        assert h == decoded
        total += count
        # Zero polar, full radical. This isomorphism shifts z into the radical.
        g = {(0,0,0):1}
        phi = identity(11)
        phi[1][1] = phi[2][2] = phi[1][3] = phi[10][10] = 2
        count, decoded = check(k,2,g,g,phi)
        assert decoded == [[1,0],[0,2]]
        total += count
    print(f"{total} ordinary isotopy equations checked across both fields; "
          "all four output legs decoded, including both radical-shear cases.")
