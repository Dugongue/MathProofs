"""Independent signed orbit checks and regression tests. Python standard library."""
from itertools import product
from random import Random

from compiler import SIGNS, Unresolved, compile_pair, eliminate, enumerate_profile, flatten, profile


def small_group(n):
    for vals in product(range(3), repeat=n*n):
        det = vals[0] if n == 1 else (vals[0]*vals[3] - vals[1]*vals[2]) % 3
        if det:
            yield vals, int(det == 2)


def orbit(shape, source):
    states = {(tuple(source), (0, 0, 0))}
    for axis, dim in enumerate(shape):
        new = set()
        stride = 1
        for n in shape[axis+1:]:
            stride *= n
        for mat, bit in small_group(dim):
            for t, signs in states:
                out = []
                for i in range(len(t)):
                    s = i // stride % dim
                    out.append(sum(mat[s*dim+j]*t[i+(j-s)*stride] for j in range(dim)) % 3)
                new.add((tuple(out), signs[:axis] + (bit,) + signs[axis+1:]))
        states = new
    table = {}
    for t, signs in states:
        table.setdefault(t, set()).add(signs)
    return table


def main():
    rng = Random(231)
    cases = 0
    for shape, source in [((1,1,1),[1]), ((2,1,2),[1,0,0,1]),
                          ((2,2,2),[0,1,1,0,1,0,0,0]), ((2,2,2),[1,0,0,0,0,0,0,1]),
                          ((2,2,2),[0,1,2,0,0,0,0,0])]:
        lookup = orbit(shape, source)
        examples = rng.sample(sorted(lookup), min(10,len(lookup)))
        examples.extend([tuple([0]*len(source)), tuple(source)])
        for t in examples:
            assert profile(shape, source, list(t)) == lookup.get(t,set())
            cases += 1

    # Compare kernel dualization to direct enumeration of both input maps.
    for shape in [(2,2,3), (2,2,4)]:
        m,n,k = shape
        for _ in range(12):
            src = [rng.randrange(3) for _ in range(m*n*k)]
            tgt = [rng.randrange(3) for _ in range(m*n*k)]
            if _ % 2:
                tgt = [(-x if i < n*k else x) % 3 for i,x in enumerate(src)]
            a,b = [flatten(shape, s, (0,1,2)) for s in (src,tgt)]
            if min(len(eliminate(v)[1]) for v in [a,b]) == k:
                direct = enumerate_profile(m, n, a, b)
                assert profile(shape, src, tgt) == direct
                cases += 1

    # Kronecker shift pencil, recursively reducing (2,n,n+1) to (2,n-1,n).
    for n in (2,3,4,5,6,7,8,9):
        shape = (2,n,n+1)
        t = [int(k == j+i) for i in range(2) for j in range(n) for k in range(n+1)]
        assert (0,0,0) in profile(shape,t,t)
        u = [(-x if i < n*(n+1) else x) % 3 for i,x in enumerate(t)]
        signs = profile(shape,t,u)
        assert signs == {(a^1,b,c) for a,b,c in profile(shape,t,t)}
        assert compile_pair(dict(shape=shape,source=t,target=u))['target'] == [int((0,0,0) not in signs)]
        cases += 1

    t = [int(i == j == k) for i,j,k in product(range(3),repeat=3)]
    try:
        compile_pair(dict(shape=(3,3,3),source=t,target=[(-x if i<9 else x)%3 for i,x in enumerate(t)]))
    except Unresolved:
        pass
    else:
        raise AssertionError("unhandled core reported as compiled")
    print(f"Passed {cases} profile cases and unsupported-core handling.")


if __name__ == '__main__':
    main()
