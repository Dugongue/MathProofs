"""Run from the same directory as flag_transport.py with Python 3."""
import json
from collections import Counter
from itertools import product

import flag_transport as ft


def det(a):
    return ft.rref(a,len(a))[2]


def check_raw():
    inputs = (
        ((1,0,0,0),(0,0,0,1)),
        ((1,0,1,0),(1,0,1,1)),
        ((1,0,0,0),(0,1,0,0)),
    )
    gl = [((a,b),(c,d)) for a,b,c,d in product(range(3),repeat=4) if (a*d-b*c)%3]
    trials = yes = 0
    for source in inputs:
        _,pivots,_ = ft.rref(source,4)
        cols = lambda rows: tuple(tuple(row[j] for j in pivots) for row in rows)
        right = ft.inv(cols(source))
        for target in inputs:
            attained = set()
            for p,q in product(gl,repeat=2):
                transformed = ft.mul(target,ft.tensor((p,q)))
                s = ft.mul(cols(transformed),right)
                if ft.mul(s,source) == transformed:
                    attained.add((det(p),det(q),det(s)))
            for desired in product((1,2),repeat=3):
                result = ft.solve_raw(source,target,2,2,desired)
                assert (result is not None) == (desired in attained)
                trials += 1
                yes += result is not None
    return dict(determinant_queries=trials,feasible=yes,negative=trials-yes,
                input_matrix_pairs_per_reference_test=len(gl)**2)


def algebra_maps(c):
    # Dense order 1,x,y,x^2,xy,x^3. Source y^2=x^3, target y^2=c*x^3.
    basis = ft.eye(6)
    def times(u,v):
        a,b,d,e,f,g = u
        k,l,m,n,r,s = v
        return tuple(x%3 for x in (a*k,a*l+b*k,a*m+d*k,a*n+b*l+e*k,
                                   a*r+b*m+d*l+f*k,a*s+b*n+e*l+c*d*m+g*k))
    radical = [(0,*v) for v in product(range(3),repeat=5)]
    signatures = Counter()
    zero = (0,)*6
    for x in radical:
        xx = times(x,x)
        xxx = times(xx,x)
        if times(xxx,x)!=zero:
            continue
        for y in radical:
            if times(xx,y)!=zero or times(y,y)!=xxx:
                continue
            rows, p, s = ft.rref((basis[0],x,y,xx,times(x,y),xxx),6)
            if len(p) == 6:
                signatures[s] += 1
    assert signatures == ({1:4374} if c==1 else {2:4374})
    return dict(signatures)


def compare_graded():
    for N in (4,8,12,16):
        # Evaluate all products in the canonical ordered monomial basis.
        basis = [(i,0) for i in range(N)] + [(0,1),(1,1)]
        def table(c):
            result = {}
            for a,b in basis:
                for u,v in basis:
                    i,j = a+u,b+v
                    if j == 2:
                        i,j,k = i+N-1,0,c
                    else:
                        k = 1
                    if (i,j) in basis:
                        result[(a,b),(u,v)] = ((i,j),k)
            return result
        pos,neg = table(1),table(2)
        assert set(pos)==set(neg)
        differences = [k for k in pos if pos[k]!=neg[k]]
        assert differences==[((0,1),(0,1))]
        for key,(out,c) in pos.items():
            source_sign = (-1)**sum(t[0] for t in key)
            assert ((-1)**out[0]*c-source_sign*neg[key][1])%3==0
        assert (sum(i for i,_ in basis))%2==1
    return [4,8,12,16]


def check_last_solver():
    import last_layer as ll
    from random import Random
    rng = Random(2741)
    cases = [(3,((1,),),((2,),)), (7,((1,),),((2,),)),
             (3,((1,0,0),(0,1,0),(0,0,1)),((2,0,0),(0,1,0),(0,0,1))),
             (3,((0,1),(1,0)),((1,0),(0,2))),
             (3,((0,0),(0,0)),((1,0),(0,0)))]
    checked = witnesses = 0
    for t,q,h in cases:
        s,v = ll.model(t,q),ll.model(t,h)
        d = len(v)
        def random_frame():
            frame = [list(row) for row in ft.eye(d)]
            for _ in range(3*d):
                i,j = rng.sample(range(d),2)
                frame[i] = [(a+b) % 3 for a,b in zip(frame[i],frame[j])]
            if rng.randrange(2):
                frame[0] = [(-a) % 3 for a in frame[0]]
            return tuple(map(tuple,frame))
        A,B,C = (random_frame() for _ in range(3))
        target = ft.mul(C,ft.mul(v,ft.tensor((ft.inv(A),ft.inv(B)))))
        got_t, got_q, _ = ll.recover(target)
        assert got_t==t and len(got_q)==len(h)
        eligible = set()
        # Independent two-variable check for these explicit diagonal/hyperbolic forms.
        if (q,h) != (((0,0),(0,0)),((1,0),(0,0))):
            if len(q)%2:
                eligible.add((2*det(A)%3,2*det(B)%3,2*det(C)%3))
            else:
                for a in (1,2):
                    sign = pow(a,t*(t+1)//2+len(q),3)
                    eligible.add(tuple(sign*det(g)%3 for g in (A,B,C)))

        for desired in product((1,2),repeat=3):
            actual = ll.solve(s,target,desired)
            assert (actual is not None)==(desired in eligible)
            witnesses += actual is not None
            checked += 1
    return dict(scrambled_pairs=len(cases),determinant_queries=checked,feasible=witnesses)


def check_ferrers():
    n = 4
    source = tuple(ft.eye(n*n)[i*n+j] for i,j in product(range(n),repeat=2)
                   if i//2+j//2>=1)
    target = (tuple(2*x % 3 for x in source[0]),*source[1:])
    widths = [ft.intrinsic_frame(source,n,n,k)[1] for k in (0,1)]
    assert widths == [[2,2],[2,2]]
    assert ft.solve_raw(source,target,n,n,(1,1,1)) is None
    assert ft.solve_raw(source,target,n,n,(1,1,2)) is not None
    return dict(dimensions=[n,n,len(source)],source_widths=widths,
                reflected_SL=False,reflected_signature=[1,1,2])


if __name__ == "__main__":
    print(json.dumps(dict(raw=check_raw(),ferrers=check_ferrers(),quadratic_solver=check_last_solver(),degree_four_source_automorphisms=algebra_maps(1),
                          degree_four_cross_isomorphisms=algebra_maps(2),
                          truncation_lengths=compare_graded()),indent=2))
