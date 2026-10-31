if not __debug__:
    raise RuntimeError("Run without -O so the exact checks remain enabled")
"""Exact checks for the credited classical design. No third-party packages."""
from pathlib import Path
from itertools import combinations
from collections import Counter
import hashlib,json
r=Path(__file__).resolve().parent
w=json.loads((r/'witness.json').read_text(encoding='utf-8'))
assert (w['points'],w['k'],w['lambda'])==(16,4,3)
D=[frozenset(t) for t in w['directions']]
assert len(D)==15 and len(set(D))==15
for t in D:
 assert len(t)==3 and all(1<=x<=15 for x in t)
 a,b,c=t; assert a^b^c==0
assert Counter(x for t in D for x in t)==Counter({i:3 for i in range(1,16)})
B=[frozenset(b) for b in w['blocks']]
assert len(B)==60 and len(set(B))==60
assert all(len(b)==4 and b<=frozenset(range(16)) for b in B)
expected={frozenset(a^x for x in ({0}|set(t))) for t in D for a in range(16)}
assert set(B)==expected
counts=Counter(pair for b in B for pair in combinations(sorted(b),2))
assert counts==Counter({p:3 for p in combinations(range(16),2)})
assert Counter(x for b in B for x in b)==Counter({i:15 for i in range(16)})
# A certificate node branches on ALL remaining triples covering its chosen point.
# A leaf is valid only when that point cannot be covered.
cert=json.loads((r/'local-refutation.json').read_text(encoding='utf-8'))
nodes=0
def check(node,remaining):
 global nodes
 nodes+=1
 a=node['point']; assert a in remaining
 options={i for i,t in enumerate(D) if a in t and t<=remaining}
 branches=node['branches']; ids=[b['direction'] for b in branches]
 assert len(ids)==len(set(ids)) and set(ids)==options
 for b in branches:check(b['child'],remaining-D[b['direction']])
check(cert,frozenset(range(1,16)))
# An independently organized exact search checks every point, not only point zero.
def pencil_count(todo,triples):
 if not todo:return 1
 x=min(todo)
 return sum(pencil_count(todo-t,[u for u in triples if not u&t]) for t in triples if x in t and t<=todo)
local={str(v):pencil_count(frozenset(range(16))-{v},[b-{v} for b in B if v in b]) for v in range(16)}
assert all(c==0 for c in local.values())
# Explicit Singer cycle: coordinates 1,2,4,8 have these images.
cols=[13,3,12,6]
def lin(x):
 y=0
 for i in range(4):
  if x>>i&1:y^=cols[i]
 return y
images=[lin(x) for x in range(16)]
assert len(set(images))==16 and {frozenset(images[x] for x in t) for t in D}==set(D)
x=1;orbit=[]
while x not in orbit:orbit.append(x);x=images[x]
assert len(orbit)==15 and x==1
t=D[0];line_orbit=[]
while t not in line_orbit:line_orbit.append(t);t=frozenset(images[x] for x in t)
assert len(line_orbit)==15
out={'status':'PASS','points':16,'blocks':60,'pairs':120,'pair_multiplicity':3,'replication':15,'refutation_nodes':nodes,'local_pencils_per_point':local,'Singer_point_orbit':15,'Singer_direction_orbit':15,'witness_sha256':hashlib.sha256((r/'witness.json').read_bytes()).hexdigest(),'scope':'Exact finite verification of a classical construction; not a new-discovery or Lean claim'}
(r/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n',encoding='utf-8')
print(json.dumps({'status':'PASS','blocks':60,'pairs':120,'refutation_nodes':nodes,'all_local_pencils_zero':True,'Singer_orbit':15}))
