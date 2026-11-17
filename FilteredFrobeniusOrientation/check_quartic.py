import itertools,json,random
from pathlib import Path
rng=random.Random(17112026)
def det(a):
 a=[r[:] for r in a];n=len(a);d=1
 for k in range(n):
  j=next((i for i in range(k,n) if a[i][k]%3),None)
  if j is None:return 0
  if j!=k:a[k],a[j]=a[j],a[k];d=-d
  pivot=a[k][k]%3;d=d*pivot%3
  inv=pow(pivot,-1,3)
  for i in range(k+1,n):
   c=a[i][k]*inv%3
   for t in range(k,n):a[i][t]=(a[i][t]-c*a[k][t])%3
 return d%3
def inv(a):
 n=len(a);a=[r[:]+[int(i==j) for j in range(n)] for i,r in enumerate(a)]
 for k in range(n):
  j=next(i for i in range(k,n) if a[i][k]%3);a[k],a[j]=a[j],a[k]
  u=pow(a[k][k],-1,3);a[k]=[x*u%3 for x in a[k]]
  for i in range(n):
   if i!=k:
    c=a[i][k];a[i]=[(x-c*y)%3 for x,y in zip(a[i],a[k])]
 return [r[n:] for r in a]
def mm(a,b):return [[sum(x*y for x,y in zip(r,c))%3 for c in zip(*b)] for r in a]
def mv(a,v):return [sum(x*y for x,y in zip(r,v))%3 for r in a]
def gl(e):
 while True:
  a=[[rng.randrange(3) for _ in range(e)] for _ in range(e)]
  if det(a):return a
def sym2(g):
 e=len(g);pairs=list(itertools.combinations_with_replacement(range(e),2));ix={a:i for i,a in enumerate(pairs)};h=len(pairs);s=[[0]*h for _ in range(h)]
 for c,(i,j) in enumerate(pairs):
  for p in range(e):
   for q in range(e):
    r=ix[tuple(sorted((p,q)))];s[r][c]=(s[r][c]+g[p][i]*g[q][j])%3
 return s
checks=0
for e in range(1,10):
 for _ in range(25):
  g=gl(e);gi=inv(g);s=sym2(g)
  assert det(s)==pow(det(g),e+1,3)
  for lam in [1,2]:
   blocks=[[[1]],g,s,[[lam*gi[j][i]%3 for j in range(e)] for i in range(e)],[[lam]]]
   n=sum(len(b) for b in blocks);a=[[0]*n for _ in range(n)];off=0
   for b in blocks:
    for i,row in enumerate(b):a[off+i][off:off+len(b)]=row
    off+=len(b)
   value=det(a);expected=pow(lam*det(g)%3,e+1,3)
   assert value==expected
   if e%4==3:assert value==1
   checks+=1
# Explicit nondegenerate quartic functionals and complete multiplication-table verification.
def algebra(e,F):
 pairs=list(itertools.combinations_with_replacement(range(e),2));h=len(pairs);n=2+2*e+h;z0=1+e+h;top=n-1
 t=[[[0]*n for _ in range(n)] for _ in range(n)]
 for i in range(n):t[0][i][i]=t[i][0][i]=1
 for k,(i,j) in enumerate(pairs):t[1+i][1+j][1+e+k]=t[1+j][1+i][1+e+k]=1
 for i in range(e):
  t[1+i][z0+i][top]=t[z0+i][1+i][top]=1
  for k,(j,l) in enumerate(pairs):
   for m in range(e):t[1+i][1+e+k][z0+m]=t[1+e+k][1+i][z0+m]=F[tuple(sorted((i,j,l,m)))]
 for k,(i,j) in enumerate(pairs):
  for l,(a,b) in enumerate(pairs):t[1+e+k][1+e+l][top]=F[tuple(sorted((i,j,a,b)))]
 return t
def product(t,a,b):
 n=len(t);out=[0]*n
 for i,x in enumerate(a):
  if x:
   for j,y in enumerate(b):
    if y:
     for k,z in enumerate(t[i][j]):out[k]=(out[k]+x*y*z)%3
 return out
raw=0
for e in [3,4]:
 mons=list(itertools.combinations_with_replacement(range(e),4));pairs=list(itertools.combinations_with_replacement(range(e),2))
 while True:
  F={m:rng.randrange(3) for m in mons};cat=[[F[tuple(sorted(a+b))] for b in pairs] for a in pairs]
  if det(cat):break
 t=algebra(e,F);n=len(t)
 # Exact associativity on all basis triples.
 for i,j,k in itertools.product(range(n),repeat=3):
  left=[sum(t[i][j][a]*t[a][k][b] for a in range(n))%3 for b in range(n)]
  right=[sum(t[j][k][a]*t[i][a][b] for a in range(n))%3 for b in range(n)]
  assert left==right
 for _ in range(5):
  g=gl(e);gi=inv(g);lam=rng.choice([1,2]);Fp={}
  for mon in mons:
   val=0
   for ks in itertools.product(range(e),repeat=4):
    weight=1
    for k,j in zip(ks,mon):weight=weight*gi[k][j]%3
    val+=weight*F[tuple(sorted(ks))]
   Fp[mon]=lam*val%3
  tp=algebra(e,Fp);blocks=[[[1]],g,sym2(g),[[lam*gi[j][i]%3 for j in range(e)] for i in range(e)],[[lam]]];a=[[0]*n for _ in range(n)];off=0
  for b in blocks:
   for i,row in enumerate(b):a[off+i][off:off+len(b)]=row
   off+=len(b)
  cols=list(map(list,zip(*a)))
  for i,j in itertools.product(range(n),repeat=2):assert mv(a,t[i][j])==product(tp,cols[i],cols[j])
  raw+=1
result={'determinant_cases':checks,'raw_algebra_isomorphisms':raw,'associativity_basis_triples':14**3+20**3,'status':'PASS','scope':'Finite controls of determinant formula and explicit examples; not a proof or a complexity certificate.'}
Path(__file__).with_name('quartic-controls.json').write_text(json.dumps(result,indent=2));print(json.dumps(result))
