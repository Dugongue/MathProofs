# Exact finite-field utilities from prior MathProof density controls.
# Diagnostic support only; no universal theorem is certified by execution.
from itertools import product, combinations
from fractions import Fraction

class Field:
 def __init__(self,q):
  self.q=q; self.p=2 if q==4 else q
  self.add=lambda a,b:(a^b) if q==4 else (a+b)%q
  self.neg=lambda a:a if q==4 else (-a)%q
  if q==4:
   def mul(a,b):
    z=0
    while b:
     if b&1:z^=a
     b>>=1;a<<=1
     if a&4:a^=7
    return z
   self.mul=mul
  else:self.mul=lambda a,b:a*b%q
  self.inv=lambda a:next(b for b in range(1,q) if self.mul(a,b)==1)
 def sum(self,v):
  z=0
  for a in v:z=self.add(z,a)
  return z
 def rref(self,rows):
  a=[list(x) for x in rows if any(x)];r=0
  if not a:return ()
  for j in range(len(a[0])):
   i=next((i for i in range(r,len(a)) if a[i][j]),None)
   if i is None:continue
   a[r],a[i]=a[i],a[r];c=self.inv(a[r][j]);a[r]=[self.mul(x,c) for x in a[r]]
   for i in range(len(a)):
    if i!=r and a[i][j]:
     c=a[i][j];a[i]=[self.add(x,self.neg(self.mul(c,y))) for x,y in zip(a[i],a[r])]
   r+=1
   if r==len(a):break
  return tuple(tuple(x) for x in a[:r])
 def null(self,rows,N):
  a=self.rref(rows);pv=[next(i for i,x in enumerate(r) if x) for r in a];ans=[]
  for j in range(N):
   if j in pv:continue
   v=[0]*N;v[j]=1
   for r,i in zip(a,pv):v[i]=self.neg(r[j])
   ans.append(tuple(v))
  return tuple(ans)
 def spaces(self,N,k):
  for pv in combinations(range(N),k):
   free=[(i,j) for i in range(k) for j in range(pv[i]+1,N) if j not in pv]
   for vals in product(range(self.q),repeat=len(free)):
    a=[[int(j==pv[i]) for j in range(N)] for i in range(k)]
    for (i,j),v in zip(free,vals):a[i][j]=v
    yield tuple(tuple(v) for v in a)
 def mm(self,A,B,n):return tuple(self.sum(self.mul(A[i*n+k],B[k*n+j]) for k in range(n)) for i in range(n) for j in range(n))
 def beta(self,A,B,n):return self.sum(self.mul(A[i*n+j],B[j*n+i]) for i in range(n) for j in range(n))
 def trace(self,A,n):return self.sum(A[i*n+i] for i in range(n))
 def good(self,H,n):
  I=tuple(int(i==j) for i in range(n) for j in range(n));powers=[I];x=I;deg=0
  for k in range(1,n+1):
   x=self.mm(x,H,n)
   if len(self.rref(powers+[x]))==len(powers):deg=k;break
   powers.append(x)
  return self.beta(H,H,n)==0 and deg==n and any(self.mm(powers[n-1],H,n))
 def hull(self,C,n):
  d=len(C);G=[tuple(self.beta(a,b,n) for b in C) for a in C]
  K=self.null(G,d)
  return self.rref([tuple(self.sum(self.mul(v[i],C[i][j]) for i in range(d)) for j in range(n*n)) for v in K])

def gaussian(N,k,q):
 z=Fraction(1)
 for i in range(k):z*=Fraction(q**N-q**i,q**k-q**i)
 assert z.denominator==1
 return z.numerator
