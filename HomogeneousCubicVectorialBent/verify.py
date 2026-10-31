from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent;D=json.loads((R/'WITNESS.json').read_text())
def gf(a,b):
 z=0
 for k in range(5):
  if b>>k&1:z^=a
  a<<=1
  if a&32:a^=37
 return z
def trace(a):
 s=a
 for _ in range(4):a=gf(a,a);s^=a
 assert s in (0,1)
 return s
def original(t):
 x=t&31;y=t>>5;out=0
 for c,k in enumerate((1,2)):
  q=trace(gf(k,gf(x,y)))
  for mask in D['g_masks'][c]:q^=(y&mask)==mask
  out|=q<<c
 return out
B=D['basis'];span={0}
for v in B:span|={x^v for x in tuple(span)}
assert len(span)==1024
L=[original(b) for b in B]
TT=[]
for x in range(1024):
 a=0;ell=0
 for j in range(10):
  if x>>j&1:a^=B[j];ell^=L[j]
 TT.append(original(a)^ell)
ANF=TT[:]
for bit in range(10):
 for x in range(1024):
  if x>>bit&1:ANF[x]^=ANF[x^(1<<bit)]
components=[]
for c in (1,2,3):
 masks=[x for x in range(1024) if (ANF[x]&c).bit_count()%2]
 assert masks and {x.bit_count() for x in masks}=={3}
 W=[1-2*((v&c).bit_count()%2) for v in TT]
 k=1
 while k<1024:
  for a in range(0,1024,2*k):
   for b in range(a,a+k):u,v=W[b],W[b+k];W[b]=u+v;W[b+k]=u-v
  k*=2
 assert {abs(v) for v in W}=={32}
 components.append({'selector':c,'monomials':masks,'degree':3,'walsh_values':sorted(set(W)),'walsh_count':len(W)})
(R/'TRUTH-TABLE.json').write_text(json.dumps(TT));(R/'CHECKS.json').write_text(json.dumps({'status':'PASS','basis_rank':10,'truth_table_sha256':hashlib.sha256(bytes(TT)).hexdigest(),'scope':'Exact full truth-table, ANF and every Walsh coefficient for all three nonzero components; informal finite certificate, not Lean','components':components},indent=2))
print(json.dumps({'status':'PASS','basis_rank':10,'component_monomial_counts':[len(c['monomials']) for c in components],'all_walsh_magnitudes':32}))
