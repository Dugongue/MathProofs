# Round-by-round finite verification of the automorphism-correction catalogue.
from itertools import product

V = range(8)
MATS = range(512)
I = 273
def act(m, v):
    return ((m & 7) if v & 1 else 0) ^ (((m >> 3) & 7) if v & 2 else 0) ^ ((m >> 6) if v & 4 else 0)
act_table = [tuple(act(m,v) for v in V) for m in MATS]
GL = [m for m in MATS if len(set(act_table[m])) == 8]
inv = {m: next(n for n in GL if all(act_table[m][act_table[n][v]] == v for v in V)) for m in GL}
def compose(a,b):
    return sum(act_table[a][act_table[b][v]] << shift for v, shift in zip((1,2,4),(0,3,6)))
def span_masks(gens):
    sub=[0]
    for g in gens:
        if g not in sub:
            sub += [v^g for v in sub]
    return sum(1<<v for v in sub)
def profile(lin):
    return tuple(span_masks(act_table[m][v] for m in lin) for v in range(1,8))
def rotation(p,m):
    ni=inv[m]
    return tuple(sum(1<<act_table[m][w] for w in V if p[act_table[ni][v]-1]>>w&1) for v in range(1,8))
def mat_subspaces(gens):
    spaces={frozenset([0,I])}
    for g in gens:
        spaces |= {s | frozenset(v^g for v in s) for s in spaces if g not in s}
    return spaces
def largest_sources(p,q):
    # Preprocess D plus self copies. Relative offset is anchored by I.
    allows=[a for a in MATS if all(
        (q[w-1] if w else 1) & ~p[v-1]==0
        for v,w in enumerate(act_table[a][1:],1))]
    return I in allows and all(
        span_masks(w for a in allows for w in V
                   if (q[act_table[a][v]-1] if act_table[a][v] else 1)>>w&1)==p[v-1]
        for v in range(1,8))
def catalogue():
    U=(1,2,3)
    plane=sum(1<<v for v in (0,*U))
    pools=[]
    for v in U:
        pools.append({1|1<<v} | {span_masks([v,w]) for w in (4,5,6,7)})
    spaces=set()
    for orient in product(*pools):
        gens=[m for m in MATS if all(orient[i]>>act_table[m][v]&1 for i,v in enumerate(U))]
        spaces |= mat_subspaces(gens)
    pset={profile(s) for s in spaces}
    out={}
    for p in pset:
        rep=min(rotation(p,m) for m in GL)
        out[rep]=p
    return len(spaces), len(pset), sorted(out)
spaces, raw, reps = catalogue()
assert (spaces,raw,len(reps))==(2268,803,44),(spaces,raw,len(reps))
orbits={p:{rotation(p,m) for m in GL} for p in reps}
weights={p:sum(x.bit_count() for x in p) for p in reps}
score={}
edges=0
for p in sorted(reps,key=weights.get):
    preds=[q for q in score if weights[q]<weights[p] and
           any(all(a&~b==0 for a,b in zip(qp,p)) and largest_sources(p,qp) for qp in orbits[q])]
    score[p]=1+max([score[q] for q in preds],default=0)
    edges+=len(preds)
print("operator spaces, concrete profiles, conjugacy types:", spaces,raw,len(reps))
print("strict ordered pairs, longest chain:",edges,max(score.values()))
explicit=[
    (273,8,35,129),(273,25,75),(273,1,88),(273,1,16),(273,17),(273,)]
for left,right in zip(explicit,explicit[1:]):
    p,q=profile(left),profile(right)
    assert any(all(x&~y==0 for x,y in zip(qp,p)) and largest_sources(p,qp)
               for qp in {rotation(q,m) for m in GL})
assert (edges,max(score.values()))==(193,6),(edges,max(score.values()))




def subspaces():
    return {span_masks(s) for s in product(V,repeat=3)}

def negative_profiles():
    return [(h,a) for h in subspaces()
            for a in V if not h>>a&1 and a==min(a^v for v in V if h>>v&1)]

def wrong_profiles(p, m, negatives):
    result=0
    for i,(h,a) in enumerate(negatives):
        corrected=span_masks(
            w for v in V if h>>v&1
              for w in V
              if (p[act_table[m][v]-1] if act_table[m][v] else 1)>>w&1)
        if corrected>>act_table[m][a]&1:
            result|=1<<i
    return result

negatives=negative_profiles()
assert len(negatives)==35
for generators, certificates in zip(explicit,[(324,44,364),(388,52,436),(266,309,427)]):
    p=profile(generators)
    tests={wrong_profiles(p,m,negatives) for m in MATS}
    for x,y in product(tests,repeat=2):
        assert x&y
    t0,t1,t2=(wrong_profiles(p,m,negatives) for m in certificates)
    assert not(t0&t1&t2)
print("Three-query certificates and two-query exclusions passed for the three selected new upper rungs.")
