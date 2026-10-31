from itertools import product
from pathlib import Path
import random,json
r=Path(__file__).resolve().parent;rng=random.Random(31771)
def inverse(M,p):
 n=len(M);A=[[x%p for x in row]+[int(i==j) for j in range(n)] for i,row in enumerate(M)]
 for j in range(n):
  v=next((i for i in range(j,n) if A[i][j]),None)
  if v is None:return None
  A[j],A[v]=A[v],A[j];u=pow(A[j][j],-1,p);A[j]=[x*u%p for x in A[j]]
  for i in range(n):
   if i==j:continue
   u=A[i][j];A[i]=[(x-u*y)%p for x,y in zip(A[i],A[j])]
 return [row[n:] for row in A]
def act(T,G,p):
 n=len(G[0]);S={}
 for out in product(range(n),repeat=3):
  v=sum(c*G[0][out[0]][a]*G[1][out[1]][b]*G[2][out[2]][d] for (a,b,d),c in T.items())%p
  if v:S[out]=v
 return S
checks=[]
for p in (2,3):
 gl=[];aff=[]
 for vals in product(range(p),repeat=9):
  M=[list(vals[i*3:(i+1)*3]) for i in range(3)];I=inverse(M,p)
  if I is None:continue
  gl.append(M)
  dual=[I[2][i] for i in range(3)]
  fixed=dual==[0,0,1]
  block=M[2]==[0,0,1] and inverse([row[:2] for row in M[:2]],p) is not None
  assert fixed==block
  if fixed:aff.append(M)
 checks.append({'field':p,'GL3_matrices':len(gl),'covector_stabilizers':len(aff),'all_stabilizer_identities':True})
 for _ in range(100):
  T={x:rng.randrange(p) for x in product(range(2),repeat=3)};T={x:c for x,c in T.items() if c}
  G=[rng.choice(aff) for i in range(3)];A=[[row[:2] for row in M[:2]] for M in G]
  full=act(T,G,p);small=act(T,A,p)
  assert full==small
 # variable-size rigid quotient frame: centralizing regular nilpotent and fixing e1 is identity.
 rigid=0
 J=[[0,0,0],[1,0,0],[0,1,0]]
 def mm(A,B):return [[sum(A[i][k]*B[k][j] for k in range(3))%p for j in range(3)] for i in range(3)]
 for H in gl:
  if [row[0] for row in H]==[1,0,0] and mm(H,J)==mm(J,H):
   rigid+=1;assert H==[[int(i==j) for j in range(3)] for i in range(3)]
 assert rigid==1
out={'status':'PASS','stabilizer_cases':checks,'padding_transporter_cases':200,'cyclic_auxiliary_frame_unique':True,'scope':'Exact finite stabilizer and padding checks; no tensor-system compiler replay or Lean verification'}
(r/'CHECKS.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
