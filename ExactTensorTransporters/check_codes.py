"""Finite controls for the two code transporter constructions (prime fields)."""
from itertools import permutations, product
from math import gcd

def sign(p):
    visited = set()
    cycles = 0
    for j in range(len(p)):
        if j not in visited:
            cycles += 1
            while j not in visited:
                visited.add(j)
                j = p[j]
    return (-1) ** (len(p) - cycles)

def words(cols, q):
    return {tuple(sum(a*b for a,b in zip(row,c)) % q for c in cols)
            for row in product(range(q), repeat=len(cols[0]))}

def normalized(cols, dest, mult, q):
    # Relation-preserving criterion on special incidence images, via
    # elimination with source and candidate target vectors side by side.
    r = len(cols[0])
    basis = {}
    for c, d, u in zip(cols, dest, mult):
        v = list(c) + [u*z % q for z in d]
        for i in sorted(basis):
            a = v[i]
            v = [(x-a*y) % q for x,y in zip(v,basis[i])]
        i = next((i for i in range(r) if v[i]), None)
        if i is None:
            if any(v[r:]):
                return False
        else:
            f = pow(v[i],-1,q)
            basis[i] = [(f*x) % q for x in v]
    return len(basis) == r

def frame(q, permutation, shifts, monomial):
    t = q-1
    n = len(permutation)
    m = t if monomial else 1
    s = n*m
    slotmap = [permutation[i]*m+(a+shifts[i])%m for i in range(n) for a in range(m)]
    M = 30+4*t
    while (M+4*s-1) % t:
        M += 1
    edges = []
    missing = set()
    start = 1
    for length in (1,2,M-4):
        path = [0]+list(range(start,start+length))
        missing.update(zip(path,path[1:]))
        start += length
    for i in range(M):
        for j in range(i+1,M):
            if (i,j) not in missing:
                edges.append((i,j))
    def pos(layer,j):
        return M+layer*s+j
    for layer in range(4):
        for j in range(s):
            edges.append((pos(layer,j),pos((layer+1)%4,j)))
            for a in range(4):
                edges.append((4*layer+a,pos(layer,j)))
    for j in range(s):
        successor = j//m*m+(j+1)%m
        for layer in (0,1):
            edges.append((pos(layer,j),pos(layer+2,successor)))
        for k in range(2*t):
            edges.append((16+k,pos(0,j)))
    action = list(range(M))+[pos(a,j) for a in range(4) for j in slotmap]
    index = {edge:i for i,edge in enumerate(edges)}
    assert len(set(tuple(sorted(e)) for e in edges))==len(edges)
    induced = [index[(action[a],action[b])] for a,b in edges]
    assert sign(action)==sign(induced)==1
    return len(action), len(edges)

def main():
    tests = frames = 0
    for q,g in ((2,1),(3,2),(5,2)):
        A=[(1,0),(0,1),(1,1),(0,0)]
        for B in ([ (1,1),(2%q,1),(1,0),(0,0)], A,
                  [(0,1),(0,1),(1,0),(0,0)]):
            Aw=words(A,q)
            Bw=words(B,q)
            for monomial in (False,True):
                for p in permutations(range(4)):
                    for shift in product(range(q-1 if monomial else 1), repeat=4):
                        scales = [pow(g,a,q) for a in shift]
                        dest = [B[j] for j in p]
                        transported = {tuple(scales[i]*v[j]%q for i,j in enumerate(p)) for v in Bw}
                        assert (Aw==transported) == normalized(A,dest,scales,q)
                        tests += 1
                        if B==A and p in ((0,1,2,3),(1,0,3,2)) and len(set(shift))==1:
                            R,E=frame(q,p,shift,monomial)
                            D=2*E-1-(q-1)*2
                            scalar_kernel=[(u,w) for u,w in product(range(1,q),repeat=2)
                                if pow(u,R,q)==pow(w,E,q)==pow(u*w,D,q)==1]
                            assert scalar_kernel == [(1,1)] and gcd(gcd(E,D),q-1)==1
                            frames += 1
    print(f"PASS: {tests} code-transport comparisons and {frames} scaffold/determinant controls.")

if __name__=="__main__":
    main()
