from fractions import Fraction as F
from itertools import product
from pathlib import Path
import json,time
P=Path(__file__).parent
zero=(F(0),F(0));one=(F(1),F(0))
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):return (x[0]*y[0]+41*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def scale(x,a):return (a*x[0],a*x[1])
def sign(x):
 a,b=x
 if b==0:return (a>0)-(a<0)
 if a==0:return (b>0)-(b<0)
 if a>0 and b>0:return 1
 if a<0 and b<0:return -1
 d=a*a-41*b*b
 return ((d>0)-(d<0))*(1 if a>0 else -1)
def qsum(xs):
 a,b=F(0),F(0)
 for x,y in xs:a+=x;b+=y
 return a,b
D=[[1,1,0],[1,1,1],[0,1,1]]
C=[[(F(2,5),F(6,205)),(F(0),F(8,205)),(F(-2,5),F(6,205))],[(F(0),F(8,205)),(F(0),F(-3,205)),(F(0),F(8,205))],[(F(-2,5),F(6,205)),(F(0),F(8,205)),(F(2,5),F(6,205))]]
wi=[F(1),F(2),F(1)];Y=[[scale(C[i][j],F(5,4)*wi[i]*wi[j]) for j in range(3)] for i in range(3)]
for i,j in product(range(3),repeat=2):assert qsum(mul(Y[i][s],Y[s][j]) for s in range(3))==(one if i==j else zero)
assert qsum(C[i][j] for i,j in product(range(3),repeat=2) if D[i][j])==(F(4,5),F(1,5))
start=time.time();rows=[]
for k in [1,2]:
 words=list(product(range(3),repeat=k));N=len(words)
 A=[[int(all(D[a][b] for a,b in zip(x,y))) for y in words] for x in words]
 W=[[one for y in words] for x in words]
 for i,x in enumerate(words):
  for j,y in enumerate(words):
   z=one
   for a,b in zip(x,y):z=mul(z,C[a][b])
   W[i][j]=z
 weights=[]
 for x in words:
  z=F(1)
  for a in x:z*=F(1,4) if a==1 else F(1)
  weights.append(z)
 sums=[F(0)]*(1<<N)
 for m in range(1,1<<N):b=m&-m;sums[m]=sums[m^b]+weights[b.bit_length()-1]
 masks=[sum(A[i][j]<<j for j in range(N)) for i in range(N)]
 count=0;max_square=F(0);max_dual=None
 for rr in range(1,1<<N):
  inds=[i for i in range(N) if rr>>i&1];common=(1<<N)-1
  for i in inds:common&=masks[i]
  scores=[qsum(W[i][j] for i in inds) for j in range(N)]
  cc=common
  while cc:
   cols=[j for j in range(N) if cc>>j&1];v=qsum(scores[j] for j in cols)
   assert sign(add(one,scale(v,-1)))>=0,(k,rr,cc,v)
   if max_dual is None or sign(add(v,scale(max_dual,-1)))>0:max_dual=v
   area=sums[rr]*sums[cc];max_square=max(max_square,area);count+=1;cc=(cc-1)&common
 assert max_square==F(25,16)**k
 objective=qsum(W[i][j] for i,j in product(range(N),repeat=2) if A[i][j]);expected=one
 for _ in range(k):expected=mul(expected,(F(4,5),F(1,5)))
 assert objective==expected
 rows.append({'tensor_power':k,'all_allowed_rectangles_checked':count,'weighted_rectangle_norm_square_max':str(max_square),'dual_objective_in_Qsqrt41':[str(z) for z in objective],'all_dual_constraints_exact':True})
cert=json.loads((P/'SHITOV-CERTIFICATE.json').read_text(encoding='utf8'));B=cert['matrix'];seen=set()
for r in cert['rectangles']:
 for i,j in product(r['rows'],r['columns']):
  assert B[i//5][j//5]*B[i%5][j%5]==1 and (i,j) not in seen;seen.add((i,j))
assert len(seen)==225 and len(cert['rectangles'])==24
report={'status':'PASS','arithmetic':'Exact Fraction and Q(sqrt41), no floating solver','domino_controls':rows,'polar_dual_matrix_squared_is_identity':True,'credited_shitov_rectangles':24,'credited_shitov_ones_covered_exactly':225,'elapsed_s':time.time()-start,'scope':'Finite exact controls; universal all-k theorem is the written proof, not inferred from these cases.'}
(P/'CONTROLS.json').write_text(json.dumps(report,indent=2),encoding='utf8');print(json.dumps(report,indent=2))
