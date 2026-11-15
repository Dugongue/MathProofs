"""Finite controls for the informal central-extension-coset proof.

Enumerates tiny objects; not the polynomial-time Luks--Miyazaki algorithm.
"""
from itertools import product
from math import gcd, prod
from pathlib import Path
import json
import random


class Group:
    def __init__(self, mods):
        self.mods=mods
        self.elements=list(product(*(range(m) for m in mods)))
        self.index={x:i for i,x in enumerate(self.elements)}
        self.n=len(self.elements)
        self.add=[[self.index[tuple((x+y)%m for x,y,m in zip(a,b,mods))]
                   for b in self.elements] for a in self.elements]
        self.neg=[self.index[tuple(-x%m for x,m in zip(a,mods))] for a in self.elements]
        self.gens=[self.index[tuple(int(i==j) for j in range(len(mods)))] for i in range(len(mods))]

    def scale(self,k,a):
        return self.index[tuple(k*x%m for x,m in zip(self.elements[a],self.mods))]

    def closure(self, gens):
        ans={0}; todo=[0]
        for x in todo:
            for g in gens:
                y=self.add[x][g]
                if y not in ans:
                    ans.add(y);todo.append(y)
        return frozenset(ans)

    def subgroups(self):
        initial=frozenset({0}); seen={initial}; todo=[initial]
        for s in todo:
            for x in range(self.n):
                if x not in s:
                    t=self.closure(tuple(s)+(x,))
                    if t not in seen:
                        seen.add(t);todo.append(t)
        return todo

    def autos(self):
        out=[]
        for images in product(range(self.n),repeat=len(self.mods)):
            if any(self.scale(m,g)!=0 for m,g in zip(self.mods,images)):
                continue
            mp=[]
            for x in self.elements:
                v=0
                for c,g in zip(x,images):v=self.add[v][self.scale(c,g)]
                mp.append(v)
            if len(set(mp))==self.n:out.append(tuple(mp))
        return out


def check_unit_orbits():
    cases=0
    for modulus,triangular,copies in [(4,False,1),(2,True,2),(3,True,1)]:
        ring=[r for r in product(range(modulus),repeat=4) if not triangular or r[2]==0]
        units=[r for r in ring if gcd(r[0]*r[3]-r[1]*r[2],modulus)==1]
        points=list(product(range(modulus),repeat=2*copies))
        def act(r,x):
            return tuple(v for j in range(copies) for v in
                         ((r[0]*x[2*j]+r[1]*x[2*j+1])%modulus,
                          (r[2]*x[2*j]+r[3]*x[2*j+1])%modulus))
        spans={x:frozenset(act(r,x) for r in ring) for x in points}
        orbits={x:frozenset(act(r,x) for r in units) for x in points}
        for x in points:
            for y in points:
                assert (spans[x]==spans[y]) == (y in orbits[x])
                cases+=1
    return cases


def check_affine():
    rng=random.Random(815)
    pair_checks=action_checks=0
    for mods,p in [((4,4),2),((2,8),2),((9,),3),((3,3),3),((2,2,2),2)]:
        b=Group(mods); groups=b.subgroups(); autos=b.autos()
        k=frozenset(b.scale(p,x) for x in range(b.n))
        coset_k=lambda x:min(b.add[x][z] for z in k)
        top=lambda u:frozenset(coset_k(x) for x in u)
        pairs=[(u,v) for u in groups for v in groups if top(u)==top(v) and u&k==v&k]
        rng.shuffle(pairs)
        for u,v in pairs[:100]:
            d=top(u);w=u&k
            coset_w=lambda x:min(b.add[x][z] for z in w)
            su={x:min(a for a in u if coset_k(a)==x) for x in d}
            sv={x:min(a for a in v if coset_k(a)==x) for x in d}
            delta={x:coset_w(b.add[sv[x]][b.neg[su[x]]]) for x in d}
            # Difference sections really are F_p-linear into (K/W)[p].
            assert all(delta[x] in k and b.scale(p,delta[x]) in w for x in d)
            assert all(delta[coset_k(b.add[x][y])] == coset_w(b.add[delta[x]][delta[y]])
                       for x in d for y in d)
            predicted=set();actual=set()
            for g in autos:
                if frozenset(g[x] for x in u)==v:actual.add(g)
                if frozenset(coset_k(g[x]) for x in d)!=d or frozenset(g[x] for x in w)!=w:
                    continue
                inverse_d={coset_k(g[x]):x for x in d}
                bg={x:coset_w(b.add[g[su[inverse_d[x]]]][b.neg[su[x]]]) for x in d}
                if bg==delta:predicted.add(g)
                assert all(bg[coset_k(b.add[x][y])] == coset_w(b.add[bg[x]][bg[y]])
                           for x in d for y in d)
                action_checks+=1
            assert predicted==actual
            pair_checks+=1
    # Identical top and intersection must not be treated as sufficient.
    b=Group((4,4));u=b.closure([b.index[1,0]]);v=b.closure([b.index[1,2]])
    k=frozenset(b.scale(2,x) for x in range(b.n))
    assert u!=v and u&k==v&k
    assert {tuple(c%2 for c in b.elements[x]) for x in u} == {tuple(c%2 for c in b.elements[x]) for x in v}
    return pair_checks,action_checks


def check_automorphism_indices():
    checked=[]
    for mods,p in [((2,4),2),((4,4),2),((2,8),2),((3,3),3),((2,2,2),2),((9,),3)]:
        b=Group(mods);autos=b.autos();same={m:[i for i,v in enumerate(mods) if v==m] for m in set(mods)}
        kernel=[];borel=[];images=set()
        for g in autos:
            blocks=[];is_kernel=True;is_borel=True
            for m,idx in sorted(same.items()):
                block=tuple(tuple(b.elements[g[b.gens[j]]][i]%p for j in idx) for i in idx)
                blocks.append(block)
                is_kernel &= all(block[i][j]==int(i==j) for i in range(len(idx)) for j in range(len(idx)))
                is_borel &= all(block[i][j]==0 for i in range(len(idx)) for j in range(i))
            images.add(tuple(blocks))
            if is_kernel:kernel.append(g)
            if is_borel:borel.append(g)
        flag_count=prod(prod((p**j-1)//(p-1) for j in range(1,len(idx)+1)) for idx in same.values())
        assert len(autos)==len(borel)*flag_count
        order=len(kernel)
        while order>1 and order%p==0:order//=p
        assert order==1
        gl_count=prod(prod(p**len(idx)-p**j for j in range(len(idx))) for idx in same.values())
        assert len(images)==gl_count and len(autos)==gl_count*len(kernel)
        checked.append({'cyclic_orders':mods,'automorphisms':len(autos),'kernel_order':len(kernel),
                        'solvable_preimage_order':len(borel),'index':flag_count})
    return checked


def main():
    unit=check_unit_orbits()
    pairs,actions=check_affine()
    indices=check_automorphism_indices()
    result={'status':'PASS','unit_orbit_comparisons':unit,'complement_pairs':pairs,
            'affine_action_controls':actions,'automorphism_quotient_controls':indices,
            'scope':'Finite correctness controls, not a Lean certificate or polynomial-time implementation.'}
    Path(__file__).with_name('CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(result))


if __name__=='__main__':main()
