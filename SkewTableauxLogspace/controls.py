"""Independent exact controls; ordinary RAM arithmetic, not an FL implementation."""
import math,json,hashlib,time
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

def det(a):
 a=[[Fraction(x) for x in row] for row in a]; n=len(a); z=Fraction(1)
 for i in range(n):
  pivot=next((j for j in range(i,n) if a[j][i]),None)
  if pivot is None:return Fraction(0)
  if pivot!=i:a[i],a[pivot]=a[pivot],a[i];z=-z
  p=a[i][i];z*=p
  for j in range(i+1,n):
   t=a[j][i]/p
   for k in range(i+1,n):a[j][k]-=t*a[i][k]
 return z

def falling(a,k):return math.prod(a-i for i in range(k))

def reduced(lam,mu):
 l=len(lam); n=sum(lam)-sum(mu)
 if not l:return 1,0,0
 mu=mu+(0,)*(l-len(mu))
 aa=[lam[l-i-1]+i for i in range(l)]
 bb=[mu[l-i-1]+i for i in range(l)]
 hh=[h for h in range(l) if h not in bb]
 kk=[b for b in bb if b>=l]; d=len(hh)
 assert d==len(kk)==sum(v>=j+1 for j,v in enumerate(mu))
 delta=math.prod(aa[j]-aa[i] for i in range(l) for j in range(i+1,l))
 DD=delta*math.factorial(l-1)
 mm=[]
 for h in hh:
  row=[]
  for k in kk:
   v=0
   for s in range(h+1):
    inner=0
    for i,a in enumerate(aa):
     di=math.prod(a-b for j,b in enumerate(aa) if j!=i)
     assert delta%di==0
     inner+=(delta//di)*falling(a,k)*math.prod(s-b for j,b in enumerate(aa) if j!=i)
    v+=(-1)**(h-s)*math.comb(h,s)*inner
   v*=math.factorial(l-1)//math.factorial(h)
   row.append(v)
  mm.append(row)
 inv=sum(l-1-h-(d-t-1) for t,h in enumerate(hh))
 ans=Fraction((-1)**inv*math.factorial(n)*delta,math.prod(math.factorial(a) for a in aa)*DD**d)*det(mm)
 assert ans.denominator==1
 return int(ans),d,inv

def aitken(lam,mu):
 l=len(lam);mu=mu+(0,)*(l-len(mu)); n=sum(lam)-sum(mu)
 a=[]
 for i in range(l):
  row=[]
  for j in range(l):
   k=lam[i]-mu[j]-i+j
   row.append(Fraction(1,math.factorial(k)) if k>=0 else 0)
  a.append(row)
 return det(a)*math.factorial(n)

@lru_cache(None)
def brute(lam,mu):
 mu=mu+(0,)*(len(lam)-len(mu))
 if lam==mu:return 1
 ans=0
 for i,v in enumerate(lam):
  if v>mu[i] and (i==len(lam)-1 or v>lam[i+1]):
   nxt=list(lam);nxt[i]-=1
   while nxt and nxt[-1]==0:nxt.pop()
   ans+=brute(tuple(nxt),mu[:len(nxt)])
 return ans

def partitions(n,m=None):
 if n==0:yield ();return
 if m is None:m=n
 for v in range(min(n,m),0,-1):
  for tail in partitions(n-v,v):yield (v,)+tail

def subparts(lam,i=0,previous=None):
 if i==len(lam):yield ();return
 top=min(lam[i],previous if previous is not None else lam[i])
 for x in range(top,-1,-1):
  for tail in subparts(lam,i+1,x):
   a=(x,)+tail
   while a and a[-1]==0:a=a[:-1]
   yield a

def main():
 start=time.time();cases=0;negative_sort=0;ranks={};examples=[]
 for total in range(11):
  for lam in partitions(total):
   for mu in set(subparts(lam)):
    value,d,inv=reduced(lam,mu)
    x=aitken(lam,mu);y=brute(lam,mu)
    assert value==x==y,(lam,mu,value,x,y)
    cases+=1;negative_sort+=inv%2;ranks[str(d)]=ranks.get(str(d),0)+1
 # Outer and inner heights and widths are unbounded in the theorem; finite larger examples exercise this geometry.
 for lam,mu in [((10,9,8,7,6,5,4,3,2,1),(9,1,1,1,1,1,1,1,1)),((20,)*12,(12,)*5),((9,8,7,6,5,4,3,2,1),(5,4,3,2,1)),((5,)*8,(4,)*8)]:
  v,d,inv=reduced(lam,mu);assert v==aitken(lam,mu)
  examples.append({'lambda':lam,'mu':mu,'d':d,'answer':str(v),'column_sign':(-1)**inv})
 result={'status':'PASS','small_exact_three_way_cases':cases,'negative_column_sort_cases':negative_sort,'rank_counts':ranks,'larger_exact_two_way_cases':examples,'seconds':time.time()-start,'methods':['direct corner-removal tableau recurrence','independent Aitken determinant','integerized interpolation low-column determinant'],'FL_implementation':False,'Lean_checks':0}
 root=Path(__file__).parent;(root/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
