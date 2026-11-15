"""Finite controls for the informal extension encoding, using no external packages.

Brute force fiber-preserving permutations is independent of the module-map test.
These checks do not verify the general algorithm or its polynomial bound.
"""
from itertools import product, permutations
from math import gcd, lcm
from pathlib import Path
import json
import random


class Abelian:
    def __init__(self, moduli):
        self.mods = tuple(moduli)
        self.els = list(product(*(range(m) for m in moduli)))
        self.zero = (0,) * len(moduli)
        self.gens = [tuple(int(i == j) for j in range(len(moduli))) for i in range(len(moduli))]
        self.exp = lcm(*moduli) if moduli else 1

    def add(self, a, b):
        return tuple((x+y) % m for x, y, m in zip(a, b, self.mods))

    def scale(self, k, a):
        return tuple(k*x % m for x, m in zip(a, self.mods))


def homs(a, b, invertible=False):
    for images in product(b.els, repeat=len(a.mods)):
        if any(b.scale(m, x) != b.zero for m, x in zip(a.mods, images)):
            continue
        mapping = {}
        for x in a.els:
            out = b.zero
            for c, im in zip(x, images):
                out = b.add(out, b.scale(c, im))
            mapping[x] = out
        if not invertible or len(a.els) == len(b.els) == len(set(mapping.values())):
            yield mapping


def extension(a, q, action, f):
    elems = list(product(a.els, q.els))
    ix = {g:i for i,g in enumerate(elems)}
    table = []
    for av, x in elems:
        row = []
        for bv, y in elems:
            row.append(ix[(a.add(a.add(av, action[x][bv]), f[x,y]), q.add(x,y))])
        table.append(row)
    # Check the concrete input independently of the cocycle validation.
    n = len(elems)
    assert all(table[0][i] == i == table[i][0] for i in range(n))
    assert all(table[table[i][j]][k] == table[i][table[j][k]]
               for i in range(n) for j in range(n) for k in range(n))
    return dict(a=a, q=q, rho=action, f=f, elems=elems, ix=ix, table=table)


def cocycles(a, q, action):
    pairs = [(x,y) for x in q.els[1:] for y in q.els[1:]]
    for vals in product(a.els, repeat=len(pairs)):
        f = {(x,y):a.zero for x in q.els for y in q.els}
        f.update(zip(pairs, vals))
        if all(a.add(action[x][f[y,z]], f[x,q.add(y,z)]) ==
               a.add(f[x,y], f[q.add(x,y),z])
               for x in q.els for y in q.els for z in q.els):
            yield f


def brute_isos(s, t):
    if len(s['elems']) != len(t['elems']):
        return set()
    q = s['q']
    fibers = [[i for i,(_,x) in enumerate(t['elems']) if x == v] for v in q.els]
    src = [[i for i,(_,x) in enumerate(s['elems']) if x == v] for v in q.els]
    options = [list(permutations(f)) for f in fibers]
    options[0] = [p for p in options[0] if p[0] == 0]
    answer = set()
    for choices in product(*options):
        mp = [0]*len(s['elems'])
        for domain, images in zip(src, choices):
            for x,y in zip(domain,images):
                mp[x] = y
        if all(mp[s['table'][i][j]] == t['table'][mp[i]][mp[j]]
               for i in range(len(mp)) for j in range(len(mp))):
            answer.add(tuple(mp))
    return answer


def module_isos(s,t,e):
    a,b,q = s['a'],t['a'],s['q']
    xs = q.els[1:]
    d = {x:tuple(int(x==y) for y in xs) for x in q.els}
    zero = (0,)*len(xs)

    def act(ext, z, vec):
        av, cs = vec
        aa = ext['a']
        out = ext['rho'][z][av]
        coeff = [0]*len(xs)
        for c,x in zip(cs,xs):
            out = aa.add(out, aa.scale(c, ext['f'][z,x]))
            for j in range(len(xs)):
                coeff[j] = (coeff[j]+c*(d[q.add(z,x)][j]-d[z][j])) % e
        return out,tuple(coeff)

    basis = [(g,zero) for g in a.gens]+[(a.zero,d[x]) for x in xs]
    answer=set()
    total=0
    for u in homs(a,b,True):
        for vv in product(b.els, repeat=len(xs)):
            for lam in range(e):
                if gcd(lam,e) != 1:
                    continue
                def linear(vec):
                    av,cs=vec
                    out=u[av]
                    for c,v in zip(cs,vv):
                        out=b.add(out,b.scale(c,v))
                    return out,tuple(lam*c % e for c in cs)
                if not all(linear(act(s,z,v)) == act(t,z,linear(v))
                           for z in q.els for v in basis):
                    continue
                inv=pow(lam,-1,e)
                mp=[]
                for av,x in s['elems']:
                    w,cs=linear((av,d[x]))
                    assert tuple(inv*c % e for c in cs)==d[x]
                    mp.append(t['ix'][b.scale(inv,w),x])
                total+=1
                answer.add(tuple(mp))
    return answer,total


def main():
    rng=random.Random(17081)
    cases=[]
    # Cyclic quotients, mixed exponents, and a noncyclic quotient.
    for mods,qmods in [((2,),(2,)),((3,),(2,)),((4,),(2,)),((2,2),(2,)),
                      ((2,),(3,)),((2,),(2,2))]:
        a,q=Abelian(mods),Abelian(qmods)
        identity={x:x for x in a.els}
        actions=[{x:identity for x in q.els}]
        if qmods==(2,) and a.exp>2:
            actions.append({q.zero:identity,q.els[1]:{x:a.scale(-1,x) for x in a.els}})
        for action in actions:
            for f in cocycles(a,q,action):
                cases.append(extension(a,q,action,f))
    pairs=[(s,t) for s in cases for t in cases
           if s['q'].mods==t['q'].mods and len(s['a'].els)==len(t['a'].els)]
    rng.shuffle(pairs)
    pairs=pairs[:180]
    positive=negative=marks=0
    for s,t in pairs:
        brute=brute_isos(s,t)
        e=lcm(s['a'].exp,t['a'].exp)
        decoded,total=module_isos(s,t,e)
        assert decoded==brute
        assert total==sum(gcd(k,e)==1 for k in range(e))*len(brute)
        positive+=bool(brute)
        negative+=not bool(brute)
        for _ in range(3):
            x=rng.randrange(len(s['elems'])); y=rng.randrange(len(t['elems']))
            assert {m for m in decoded if m[x]==y} == {m for m in brute if m[x]==y}
            marks+=1
    # The annihilator need not equal the exponent.
    for s,t in pairs[:12]:
        e=2*lcm(s['a'].exp,t['a'].exp)
        decoded,total=module_isos(s,t,e)
        brute=brute_isos(s,t)
        assert decoded==brute
        assert total==sum(gcd(k,e)==1 for k in range(e))*len(brute)
    # Diagram compatibility: centralizers and arrows between two copies.
    diagram_checks=0
    for s in cases[:12]:
        auto=brute_isos(s,s)
        decoded,_=module_isos(s,s,s['a'].exp)
        for f in sorted(auto)[:3]:
            lhs={u for u in auto if all(u[f[x]]==f[u[x]] for x in range(len(f)))}
            rhs={u for u in decoded if all(u[f[x]]==f[u[x]] for x in range(len(f)))}
            assert lhs==rhs
            diagram_checks+=1
    result=dict(status='PASS',extension_inputs=len(cases),pair_checks=len(pairs),
                isomorphic_pairs=positive,nonisomorphic_pairs=negative,
                marked_checks=marks,nonminimal_annihilator_checks=12,
                diagram_loop_checks=diagram_checks,
                scope='Finite controls only; not a formal proof or implementation of the polynomial module-isomorphism algorithm.')
    Path(__file__).with_name('CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))


if __name__=='__main__':
    main()
