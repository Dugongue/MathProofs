"""Exact reference implementation; see PROOF.md for the complexity proof."""
from fractions import Fraction as Q

def degree(factors,A,N):
 """Return degree or None, for explicit rational factors and binary integer exponents."""
 factors=[(Q(a),Q(b),e) for a,b,e in factors]
 A=Q(A)
 if type(N) is not int or N<0 or any(type(e) is not int or e<0 for a,b,e in factors):
  raise ValueError("Exponents must be nonnegative integers")
 C=Q(1);b=0;fs=[]
 for alpha,beta,e in factors:
  if e==0:C*=alpha+beta
  elif not alpha:C*=beta
  elif not beta:C*=alpha;b+=e
  else:C*=alpha;fs.append((e,beta/alpha))
 if not C:return None if not A else N
 if not fs:
  if not A:return b
  if b!=N:return max(b,N)
  return None if C==A else b
 D=b+sum(e for e,c in fs)
 if not A or N<D:return D
 if N>D:return N
 if A!=C:return D
 records={}
 def record(d,a,m):records[d,a]=records.get((d,a),0)+m
 for e,c in fs:
  if c<0:record(e,-c,1)
  else:record(2*e,c*c,1);record(e,c,-1)
 records={k:m for k,m in records.items() if m}
 assert records
 s=len(records);K=16*s*s;d0=min(d for d,a in records);M=min(sum(e for e,c in fs),K*d0);bank={}
 for (d,a),m in records.items():
  cap=M//d;assert cap<=K;ak=Q(1)
  for k in range(1,cap+1):ak*=a;bank[k*d]=bank.get(k*d,Q(0))+m*d*ak
 nu=min(v for v,c in bank.items() if c)
 return D-nu
