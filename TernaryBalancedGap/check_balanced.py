"""Sign-profile regressions at balanced terminal formats."""
from itertools import product
from random import Random

import compiler as c
from balanced import act, add, identity
from intertwiners import slice_profile


def reflected(shape, data):
    return [(-v if i < shape[1]*shape[2] else v)%3 for i,v in enumerate(data)]


def reframe(shape, data, rng):
    signs = []
    for axis,n in enumerate(shape):
        g = identity(n)
        for _ in range(3*n):
            i,j = rng.sample(range(n),2)
            g[i] = [(x+y)%3 for x,y in zip(g[i],g[j])]
        sign = rng.randrange(2)
        if sign:
            g[0] = [-x%3 for x in g[0]]
        data = act(shape,data,axis,g)
        signs.append(sign)
    return data,tuple(signs)


def direct_sum(blocks):
    offsets = [0]*3
    dims = tuple(sum(s[i] for s,t in blocks) for i in range(3))
    data = [0]*(dims[0]*dims[1]*dims[2])
    for shape,part in blocks:
        for v,(i,j,k) in zip(part,product(*(range(n) for n in shape))):
            pos = ((i+offsets[0])*dims[1]+j+offsets[1])*dims[2]+k+offsets[2]
            data[pos] = v
        offsets = [o+n for o,n in zip(offsets,shape)]
    return dims,data


def chain(d):
    return [int(sum(v)==2*(d-1)) for v in product(range(d),repeat=3)]


def main():
    rng = Random(156)
    count = 0
    even = {v for v in c.SIGNS if sum(v)%2==0}
    zero = {(0,0,0)}
    diag = {(0,0,0),(1,1,1)}
    for d in range(3,10):
        shape = (d,d,d)
        signs = [zero,even,diag,c.SIGNS][d%4]
        x,a = reframe(shape,chain(d),rng)
        y,b = reframe(shape,chain(d),rng)
        assert c.profile(shape,x,y) == {add(v,add(a,b)) for v in signs}
        count += 1

    # A volume form forces even total sign; two isomorphic odd blocks add an odd swap.
    eps = [0 if len(set(v))<3 else (-1)**sum(a>b for i,a in enumerate(v) for b in v[i+1:])%3
           for v in product(range(3),repeat=3)]
    for blocks, expected in [([((3,3,3),eps)],even),([((3,3,3),eps)]*2,c.SIGNS),
                             ([((4,4,4),chain(4)),((3,3,3),eps)],even),
                             ([((3,3,3),eps),((5,5,5),chain(5))],c.SIGNS-even),
                             ([((4,4,4),chain(4))]*2,zero)]:
        shape, x = direct_sum(blocks)
        _, y = direct_sum(blocks[::-1])
        # A 3-by-5 crossing shifts the even total-sign subgroup to the odd coset.
        x,a = reframe(shape,x,rng)
        y,b = reframe(shape,y,rng)
        assert c.profile(shape,x,y) == {add(add(a,b),v) for v in expected}
        count += 1

    # Independent two-mode exhaustive oracle for the new slice and orbit-intersection algorithms.
    for shape in [(2,2,2),(2,2,3),(2,3,2),(3,2,2)]:
        for _ in range(4):
            t = [rng.randrange(3) for _ in range(shape[0]*shape[1]*shape[2])]
            u,_ = reframe(shape,t,rng)
            largest = max(range(3),key=shape.__getitem__)
            order = [i for i in range(3) if i!=largest]+[largest]
            s,v = [c.flatten(shape,z,order) for z in (t,u)]
            if len(c.eliminate(s)[1]) != shape[largest]:
                continue
            args = (shape[order[0]],shape[order[1]],s,v)
            raw = c.enumerate_profile(*args)
            assert c.meet_profile(*args,(c.eliminate,c.matrices,c.multiply)) == raw
            want = {tuple(bits[order.index(i)] for i in range(3)) for bits in raw}
            assert slice_profile(shape,t,u,100000,c.eliminate,c.matrices,c.kernel,c.flatten)==want
            count += 1

    for n in (4,5,6):
        shape = (3,n,n)
        t = [int((i==0 and j==k) or (i==1 and (j+1)%n==k) or (i==2 and j==k==0))
             for i,j,k in product(range(3),range(n),range(n))]
        base = c.profile(shape,t,t)
        assert (0,0,0) in base
        u,b = reframe(shape,t,rng)
        assert c.profile(shape,t,u)=={add(v,b) for v in base}
        count += 1
    print(f"Passed {count} balanced-core profile checks.")


if __name__ == '__main__':
    main()
