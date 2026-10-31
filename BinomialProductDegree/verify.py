if not __debug__:
    raise RuntimeError("Run without -O so the exact checks remain enabled")
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as Q
from pathlib import Path
import json,random
from degree import degree as solve
r=Path(__file__).resolve().parent
def dense(factors,A,N):
 F={0:Q(1)}
 for a,b,e in factors:
  G={}
  for k,c in F.items():G[k+e]=G.get(k+e,Q(0))+a*c;G[k]=G.get(k,Q(0))+b*c
  F={k:c for k,c in G.items() if c}
 F[N]=F.get(N,Q(0))-A
 return max((k for k,c in F.items() if c),default=None)

rng=random.Random(3171031);cases=0
for _ in range(3000):
 fs=[(Q(rng.randrange(-4,5),rng.randrange(1,5)),Q(rng.randrange(-4,5),rng.randrange(1,5)),rng.randrange(6)) for i in range(rng.randrange(8))]
 A=Q(rng.randrange(-4,5),rng.randrange(1,5));N=rng.randrange(26)
 if rng.randrange(2):
  N=sum(e for a,b,e in fs if a and e>0);A=Q(1)
  for a,b,e in fs:A*=a+b if e==0 else a if a else b
 assert solve(fs,A,N)==dense(fs,A,N),(fs,A,N)
 cases+=1
# Binary-scale controls use exact substitution of an independently expanded small polynomial.
scaled=[]
for power in (10,100,1000,10000):
 scale=1<<power;fs=[(Q(1),Q(-2),scale),(Q(1),Q(1),scale),(Q(1),Q(1),scale)]
 got=solve(fs,Q(1),3*scale);assert got==scale
 scaled.append({'exponent_bit_length':power+1,'degree_is_scale':True})
# The identity (1-z)*product_j(1+z^(2^j))=1-z^(2^m) has a huge empty coefficient interval.
fs=[(Q(1),Q(-1),1)]+[(Q(1),Q(1),1<<j) for j in range(1000)]
# Reversal uses c=-1 and +1; product leading coefficients are all +1; D=2^1000.
assert solve(fs,Q(1),1<<1000)==0
out={'status':'PASS','independent_small_full_inputs':cases,'huge_binary_scale_cases':scaled,'unit_chain_factors':1001,'unit_chain_binary_degree_bits':1001,'scope':'Independent exact implementation compared against direct polynomial expansion; huge cases use proved scaled identities; not Lean or novelty evidence'}
(r/'CHECKS.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
