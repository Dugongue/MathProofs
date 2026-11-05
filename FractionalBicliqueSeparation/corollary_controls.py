from fractions import Fraction as F
from itertools import product,permutations
from pathlib import Path
import json,time
P=Path(__file__).parent

def rank(A):
 A=[list(map(F,r)) for r in A];r=0
 for j in range(len(A[0])):
  k=next((i for i in range(r,len(A)) if A[i][j]),None)
  if k is None:continue
  A[r],A[k]=A[k],A[r];c=A[r][j];A[r]=[v/c for v in A[r]]
  for i in range(len(A)):
   if i!=r:
    c=A[i][j];A[i]=[v-c*w for v,w in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r
start=time.time();cases=0;class2=0;rank2=0;rank3=0;byshape=[]
for m,n in product(range(1,4),repeat=2):
 rects=[]
 for R,C in product(range(1,1<<m),range(1,1<<n)):
  rects.append(sum(1<<(i*n+j) for i,j in product(range(m),range(n)) if R>>i&1 and C>>j&1))
 cnt=0
 for mask in range(1,1<<(m*n)):
  cases+=1;A=[[mask>>(i*n+j)&1 for j in range(n)] for i in range(m)]
  good=[r for r in rects if r&mask==r];one=mask in good;cover2=any(r|s==mask for r in good for s in good)
  verts=[(i,j) for i,j in product(range(m),range(n)) if A[i][j]];color={};bip=True
  for v in verts:
   if v in color:continue
   color[v]=0;todo=[v]
   while todo:
    a,b=todo.pop()
    for c,d in verts:
     if not(A[a][d] and A[c][b]):
      if (c,d) in color:
       if color[c,d]==color[a,b]:bip=False
      else:color[c,d]=1-color[a,b];todo.append((c,d))
  assert bip==cover2,(m,n,mask)
  if one or not cover2:continue
  class2+=1;cnt+=1;r=rank(A);assert r in (2,3)
  rr=[]
  for row in A:
   t=tuple(row)
   if any(t) and t not in rr:rr.append(t)
  cols=[]
  for j in range(n):
   t=tuple(row[j] for row in rr)
   if any(t) and t not in cols:cols.append(t)
  K=list(map(list,zip(*cols)));D=[[1,1,0],[1,1,1],[0,1,1]]
  domino=len(K)==3 and len(K[0])==3 and any(all(K[i][j]==D[p[i]][q[j]] for i,j in product(range(3),repeat=2)) for p in permutations(range(3)) for q in permutations(range(3)))
  assert domino==(r==3),(A,K,r)
  if r==2:
   assert len(K)<=2 or len(K[0])<=2;rank2+=1
  else:rank3+=1
 byshape.append({'rows':m,'columns':n,'nonrectangular_two_cover_cases':cnt})
r={'status':'PASS','all_nonzero_matrices_up_to_3_by_3':cases,'exact_fractional_cover_two_class_via_proved_conflict_characterization':class2,'rank_two_cases':rank2,'rank_three_Domino_kernel_cases':rank3,'by_shape':byshape,'elapsed_s':time.time()-start,'scope':'All finite matrices of each shape1..3 by1..3; exact two-rectangle covers, conflict bipartiteness, rational real rank and reduced kernels. No LP approximate inference.'}
(P/'COROLLARY-CONTROLS.json').write_text(json.dumps(r,indent=2),encoding='utf8');print(json.dumps(r,indent=2))
