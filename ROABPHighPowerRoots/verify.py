from fractions import Fraction
from pathlib import Path
import random,json
r=Path(__file__).resolve().parent; rng=random.Random(1931)
def mul(A,B):
 C={}
 for (i,j),a in A.items():
  for (k,l),b in B.items():C[i+k,j+l]=C.get((i+k,j+l),0)+a*b
 return {e:c for e,c in C.items() if c}
def rank(A):
 if not A:return 0
 n=max(i for i,j in A)+1;m=max(j for i,j in A)+1
 M=[[Fraction(A.get((i,j),0)) for j in range(m)] for i in range(n)];p=0
 for j in range(m):
  q=next((i for i in range(p,n) if M[i][j]),None)
  if q is None:continue
  M[p],M[q]=M[q],M[p];a=M[p][j];M[p]=[x/a for x in M[p]]
  for i in range(p+1,n):
   a=M[i][j]
   if a:M[i]=[x-a*y for x,y in zip(M[i],M[p])]
  p+=1
  if p==n:break
 return p
rec=[]
for case in range(100):
 G={(i,j):rng.randrange(-2,3) for i in range(4) for j in range(4)};G={a:c for a,c in G.items() if c}
 if not G:continue
 rg=rank(G)
 for d in (2,3,4):
  F={(0,0):1}
  for _ in range(d):F=mul(F,G)
  rf=rank(F)
  assert rg==1 or rf>=d+1,(G,d,rg,rf)
  rec.append({'root_rank':rg,'exponent':d,'power_rank':rf})
out={'status':'PASS','cases':len(rec),'scope':'Exact rational ranks of finite bivariate examples; not proof of general theorem or novelty','records':rec}
(r/'CHECKS.json').write_text(json.dumps(out,indent=2));print(json.dumps({'status':'PASS','cases':len(rec)}))
