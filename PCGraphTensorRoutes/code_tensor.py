"""Witness recovery for the Section 5 code tensor over prime fields.

Use the convention P T_M(x,t) = T_N(Yx,Zt). The caller supplies a genuine
isomorphism with its inverse. The result A,B satisfies A M = N B.
"""


def matmul(a, b, p):
    return [[sum(x*y for x,y in zip(row,col)) % p for col in zip(*b)] for row in a]


def eye(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]


def inverse(a, p):
    n = len(a)
    rows = [list(x)+y for x,y in zip(a,eye(n))]
    for j in range(n):
        t = next((i for i in range(j,n) if rows[i][j] % p), None)
        if t is None:
            raise ValueError("Expected an invertible matrix over the given prime field.")
        rows[j], rows[t] = rows[t], rows[j]
        u = pow(rows[j][j],-1,p)
        rows[j] = [v*u % p for v in rows[j]]
        for i in range(n):
            if i != j:
                t = rows[i][j]
                rows[i] = [(a-t*b) % p for a,b in zip(rows[i],rows[j])]
    return [row[n:] for row in rows]


def has_two_minor(a,p):
    for i,row in enumerate(a):
        for second in a[:i]:
            for j,x in enumerate(row):
                if any((x*second[h]-row[h]*second[j]) % p for h in range(j)):
                    return True
    return False


def line_basis(a,p):
    """Move the nonzero column line to the first standard coordinate."""
    k = len(a)
    v = next(col for col in zip(*a) if any(x % p for x in col))
    i = next(i for i,x in enumerate(v) if x % p)
    others = [j for j in range(k) if j != i]
    frame = [[v[t]]+[int(t==j) for j in others] for t in range(k)]
    return inverse(frame,p),frame


def decode(m, n, transform, coordinate_map, slice_map, p):
    """Return a monomial B and a data map A, in the order (A,B)."""
    k, s = len(m), len(coordinate_map)
    if not k:
        return [], eye(s)
    if has_two_minor(m,p) or has_two_minor(n,p):
        zinv = pow(slice_map[0][0],-1,p)
        a = [[zinv*transform[i][j] % p for j in range(k)] for i in range(k)]
        b = coordinate_map
    elif any(x % p for row in m for x in row):
        lm, _ = line_basis(m,p)
        ln, fn = line_basis(n,p)
        mc, nc = matmul(lm,m,p)[0],matmul(ln,n,p)[0]
        a = matmul(fn,lm,p)
        b = [[0]*s for _ in range(s)]
        for j in range(s):
            i, = [i for i in range(s) if coordinate_map[i][j] % p]
            if (mc[j]==0) != (nc[i]==0):
                raise ValueError("Matched columns disagree on vanishing.")
            b[i][j] = mc[j]*pow(nc[i],-1,p) % p if nc[i] else 1
    else:
        a, b = eye(k),eye(s)
    if matmul(a,m,p) != matmul(n,b,p):
        raise ValueError("The recovered code equation failed.")
    return a,b


def value(m,x,t,p):
    top = [t[0]*sum(a*b for a,b in zip(row,x)) % p for row in m]
    return top+[x[i]*t[1+2*i+b] % p for i in range(len(x)) for b in range(2)]


def apply(a,v,p):
    return [sum(x*y for x,y in zip(row,v)) % p for row in a]


def verify(m,n,P,Y,Z,p):
    k,s = len(m),len(Y)
    for x in eye(s):
        for t in eye(1+2*s):
            assert apply(P,value(m,x,t,p),p) == value(n,apply(Y,x,p),apply(Z,t,p),p)
    a,b = decode(m,n,P,Y,Z,p)
    assert matmul(a,inverse(a,p),p)==eye(k)
    assert matmul(b,inverse(b,p),p)==eye(s)
    return s*(1+2*s)


def cases():
    count = 0
    for p in (2,3,5,7):
        # Two independent column shears inside each private two-plane and one
        # shift from the data parameter into the block for a coloop.
        m = [[1,0,0,0],[0,1,1,0]]
        k,s = 2,4
        a = [[1,1],[0,1]]
        Y = [[0]*s for _ in range(s)]
        perm = (2,0,3,1)
        scales = [1,p-1,1,p-1]
        for j,i in enumerate(perm):
            Y[i][j] = scales[j]
        n = matmul(matmul(a,m,p),inverse(Y,p),p)
        z = p-1
        P, Z = [[0]*(k+2*s) for _ in range(k+2*s)], [[0]*(1+2*s) for _ in range(1+2*s)]
        for i in range(k):
            for j in range(k):
                P[i][j] = z*a[i][j] % p
        Z[0][0] = z
        for j,i in enumerate(perm):
            for u,row in enumerate(((1,1),(0,1))):
                for v,entry in enumerate(row):
                    Z[1+2*i+u][1+2*j+v] = entry
                    P[k+2*i+u][k+2*j+v] = entry*scales[j] % p
        Z[1+2*perm[0]][0] = 1
        P[k+2*perm[0]][0] = scales[0]
        count += verify(m,n,P,Y,Z,p)
        # A rank-one example with redundant data rows. The 00 slice entry is
        # zero in this genuine transporter, so the separate rank-one rule matters.
        m = [[1,0],[0,0]]
        P,Z,Y = eye(6),eye(5),eye(2)
        P[0],P[2] = P[2],P[0]
        Z[0],Z[1] = Z[1],Z[0]
        count += verify(m,m,P,Y,Z,p)
        count += verify([[0,0]],[[0,0]],eye(5),eye(2),eye(5),p)
    print(f"{count} tensor basis equations verified over four prime fields, "
          "including a rank-one witness with zero data-slice scalar.")


if __name__ == "__main__":
    cases()
