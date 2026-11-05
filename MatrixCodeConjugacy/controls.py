from pathlib import Path
import itertools,json,time,collections,random
OUT=Path(__file__).parent
from field_arithmetic import Field, gaussian
def lin(f,coef,basis,N):
 return tuple(f.sum(f.mul(a,v[j]) for a,v in zip(coef,basis)) for j in range(N))
def transpose(A,n):return tuple(A[j*n+i] for i in range(n) for j in range(n))
def sub(f,A,B):return tuple(f.add(a,f.neg(b)) for a,b in zip(A,B))
def eye(n):return tuple(int(i==j) for i in range(n) for j in range(n))
def inv(f,A,n):
 aug=[tuple(A[i*n+j] for j in range(n))+tuple(int(i==j) for j in range(n)) for i in range(n)]
 rr=f.rref(aug)
 if len(rr)!=n or any(rr[i][j]!=int(i==j) for i in range(n) for j in range(n)):return None
 return tuple(rr[i][n+j] for i in range(n) for j in range(n))
def conj(f,S,C,n):
 T=inv(f,S,n);assert T is not None
 return f.rref([f.mm(f.mm(S,X,n),T,n) for X in C])
def intertwiner(f,pair,target,n):
 N=n*n;rows=[]
 for X,Y in zip(pair,target):
  for i in range(n):
   for j in range(n):
    rows.append(tuple(f.add(X[b*n+j] if i==a else 0,f.neg(Y[i*n+a]) if b==j else 0) for a in range(n) for b in range(n)))
 return f.null(rows,N)
def commdim(f,pair,n):return len(intertwiner(f,pair,pair,n))
def span_elements(f,C,N):
 return [lin(f,c,C,N) for c in itertools.product(range(f.q),repeat=len(C))]
def pair_search(f,C,D,n):
 elems=span_elements(f,C,n*n);anchor=None
 for X in elems:
  for Y in elems:
   if commdim(f,(X,Y),n)==1:anchor=(X,Y);break
  if anchor:break
 if not anchor:return 'FAIL',None
 targets=span_elements(f,D,n*n)
 for U in targets:
  for V in targets:
   K=intertwiner(f,anchor,(U,V),n)
   if len(K)==1 and inv(f,K[0],n) is not None and conj(f,K[0],C,n)==D:return 'YES',K[0]
 return 'NO',None
def projection(f,R,E,n):
 k=len(E)
 if not k:return (0,)*(n*n)
 G=[tuple(f.beta(x,y,n) for y in E) for x in E]
 if len(f.rref(G))<k:return None
 rr=f.rref([tuple(g)+(f.beta(R,x,n),) for g,x in zip(G,E)])
 return lin(f,[row[-1] for row in rr],E,n*n)
def canonical_pair(f,C,n):
 hull=f.hull(C,n)
 if len(hull)!=1:return None
 H=hull[0];roots=[];I=eye(n)
 for a in range(f.q):
  T=sub(f,H,tuple(f.mul(a,x) for x in I))
  if inv(f,T,n) is None:roots.append(a)
 if len(roots)!=1 or roots[0]==0:return None
 lam=roots[0];A=tuple(f.mul(f.inv(lam),x) for x in H);T=sub(f,A,I)
 right=f.null([T[i*n:(i+1)*n] for i in range(n)],n)
 TT=transpose(T,n);left=f.null([TT[i*n:(i+1)*n] for i in range(n)],n)
 if len(right)!=1 or len(left)!=1:return None
 r,v=right[0],left[0];den=f.sum(f.mul(x,y) for x,y in zip(r,v))
 if not den:return None
 P=tuple(f.mul(f.inv(den),f.mul(r[i],v[j])) for i in range(n) for j in range(n))
 coeff=f.null([tuple(f.beta(P,X,n) for X in C)],len(C))
 E=f.rref([lin(f,c,C,n*n) for c in coeff])
 Z=projection(f,I,E,n)
 if Z is None:return None
 return A,Z
def canonical_compare(f,C,D,n):
 pair=canonical_pair(f,C,n)
 if pair is None or commdim(f,pair,n)!=1:return 'FAIL',None
 other=canonical_pair(f,D,n)
 if other is None:return 'NO',None
 K=intertwiner(f,pair,other,n)
 if len(K)!=1 or inv(f,K[0],n) is None:return 'NO',None
 S=K[0]
 return ('YES',S) if conj(f,S,C,n)==D else ('NO',None)
def main():
 t=time.time();report={'status':'PASS','scope':'Exact finite diagnostic controls, not a universal proof certificate.'}
 # Nondegenerate subspace bound: exhaustive, including extension field F4.
 nd=[]
 for q,M in [(2,1),(2,2),(2,3),(2,4),(2,5),(3,2),(3,3),(3,4),(4,2),(4,3),(4,4)]:
  f=Field(q)
  for k in range(M+1):
   total=good=0
   for C in f.spaces(M,k):
    G=[tuple(f.sum(f.mul(a,b) for a,b in zip(x,y)) for y in C) for x in C]
    total+=1;good+=len(f.rref(G))==k
   assert total==gaussian(M,k,q) and good*64>=total
   nd.append({'q':q,'M':M,'k':k,'total':total,'nondegenerate':good})
 report['nondegenerate_subspaces']=nd
 print('NONDEGENERATE_DONE',len(nd),flush=True)
 # Exhaustive all-target small-code routine, including singular and zero inputs.
 f=Field(2);n=2;N=4;groups=[A for A in itertools.product(range(2),repeat=N) if inv(f,A,n)]
 codes=list(itertools.chain.from_iterable(f.spaces(N,k) for k in range(N+1)));checks=accepted=0
 for C in codes:
  d=min(len(C),N-len(C));C0=C
  if len(C)>N/2:C0=f.null([transpose(x,n) for x in C],N)
  if d!=2:continue
  actual={conj(f,S,C,n) for S in groups}
  for D in codes:
   if len(D)!=len(C):continue
   D0=D if len(D)<=N/2 else f.null([transpose(x,n) for x in D],N)
   status,S=pair_search(f,C0,D0,n);checks+=1
   if status!='FAIL':
    accepted+=1;assert (status=='YES')==(D in actual)
    if S is not None:assert conj(f,S,C,n)==D
 report['small_branch']={'q':2,'n':2,'all_codes':len(codes),'all_dimension_two_source_target_checks':checks,'nonfailure_checks':accepted,'group_size':len(groups)}
 print('SMALL_DONE',checks,accepted,flush=True)
 # Middle-branch projection incidence: fixed good hull in M3(F2), all k<=3.
 n=3;N=9;A=(1,0,0,0,0,1,0,1,1);P=(1,0,0,0,0,0,0,0,0);I=eye(n);R=sub(f,I,A)
 assert f.beta(A,A,n)==0 and f.beta(A,P,n)==1 and f.beta(P,P,n)==1
 U=f.null([transpose(A,n),transpose(P,n)],N);M=len(U);assert M==7
 proj=[];good_codes=[];cd_cache={}
 for k in range(1,4):
  atoms=collections.Counter();total=ndcount=central=0
  for coordinates in f.spaces(M,k):
   E=[lin(f,c,U,N) for c in coordinates];total+=1
   Z=projection(f,R,E,n)
   if Z is None:continue
   ndcount+=1;atoms[Z]+=1
   if Z not in cd_cache:cd_cache[Z]=commdim(f,(A,Z),n)
   if cd_cache[Z]==1:
    central+=1
    if k==3 and len(good_codes)<12:good_codes.append(f.rref([A]+E))
  assert total==gaussian(M,k,2) and ndcount*64>=total
  for z,count in atoms.items():
   if z not in ((0,)*N,R):assert count<=gaussian(M-2,k-1,2)
  exceptional=atoms[(0,)*N]+atoms[R]
  assert exceptional<=gaussian(M-1,k,2)+gaussian(M-1,k-1,2)
  proj.append({'k':k,'all_subspaces':total,'nondegenerate':ndcount,'scalar_commutant':central,'exceptional_projections':exceptional,'distinct_projection_values':len(atoms)})
 report['projection_incidence']=proj
 print('PROJECTION_DONE',proj,flush=True)
 # All GL3(F2) conjugates of accepted middle-branch sources, plus arbitrary targets.
 groups=[S for S in itertools.product(range(2),repeat=N) if inv(f,S,n)]
 checks=0;rng=random.Random(140611)
 for C in good_codes[:4]:
  actual={conj(f,S,C,n) for S in groups}
  for D in actual:
   status,S=canonical_compare(f,C,D,n);assert status=='YES' and conj(f,S,C,n)==D;checks+=1
  for _ in range(40):
   while True:
    D=f.rref([tuple(rng.randrange(2) for _ in range(N)) for _ in range(4)])
    if len(D)==4:break
   status,S=canonical_compare(f,C,D,n)
   assert status!='FAIL' and (status=='YES')==(D in actual);checks+=1
 report['middle_branch']={'q':2,'n':3,'code_dimension':4,'accepted_sources':min(4,len(good_codes)),'all_conjugate_and_random_target_checks':checks,'group_size':len(groups)}
 assert good_codes and checks>0
 report['seconds']=round(time.time()-t,3)
 (OUT/'FINITE-CONTROLS.json').write_text(json.dumps(report,indent=2),encoding='utf-8')
 print(json.dumps({'status':'PASS','seconds':report['seconds'],'middle_checks':checks}),flush=True)
if __name__=='__main__':main()
