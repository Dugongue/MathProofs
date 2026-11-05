"""Exact coupled k=2 partial-trace fixture from the credited 27-qubit pair."""
import pathlib,sys,itertools,json,time,math,hashlib
HERE=pathlib.Path(__file__).parent;sys.path.insert(0,str(HERE));import full_controls as F
from modular_kernel import kernel_generators
from sympy import Rational
start=time.time();subs=[sum(1<<j for j in K) for k in [4,5] for K in itertools.combinations(range(6),k)]
D27=[(0,0,s|(1<<(6+j))) for j,s in enumerate(subs)]
X27=[(0,(1<<i)|sum(1<<(6+j) for j,s in enumerate(subs) if (s>>i)&1),0) for i in range(6)]
H27=[(h,x,((1<<6)-1)^(1<<i)) for i,(h,x,z) in enumerate(X27)]
keep=[j for j in range(27) if j not in [6,7]];n=len(keep);T=list(range(n))
def restrict(g):
 h,x,z=g;assert not (x|z)&((1<<6)|(1<<7));return h,sum(((x>>j)&1)<<k for k,j in enumerate(keep)),sum(((z>>j)&1)<<k for k,j in enumerate(keep))
def prod(gs,mask):
 r=(0,0,0)
 for i,g in enumerate(gs):
  if (mask>>i)&1:r=F.C.pmul(r,g)
 return r
V=F.perp(subs[:2],6);assert len(V)==4
D=[restrict(g) for g in D27[2:]];comp=[restrict(prod(X27,v)) for v in V];hc=[restrict(prod(H27,v)) for v in V]
G=D+comp;H=D+hc;assert len(G)==23 and len(H)==23 and n==25
A=[]
for y in range(64):
 z=y|sum(((s&y).bit_count()%2)<<(6+j) for j,s in enumerate(subs));A.append(sum(((z>>j)&1)<<k for k,j in enumerate(keep)))
K=F.rr([F.label(g,n)&~(((1<<n)-1)<<n) for g in G]);F.data=lambda gs,t,nn:(D,comp,A,K)
Q=1<<(2+n*(n+1).bit_length());F.snf=lambda M:kernel_generators(M,Q)
checks=0
def exact(gs,hs,nn,q,ph):
 global checks
 assert hs[:len(D)]==D
 for h,x,z in hs:assert (h-(x&z).bit_count())%2==0
 for a,b in itertools.combinations(hs,2):assert ((a[1]&b[2]).bit_count()+(a[2]&b[1]).bit_count())%2==0
 for (h,x,z),(hp,xp,zp) in zip(gs,hs):
  assert x==xp
  for y in A:
   left=sum(ph[j]*(((x>>j)&1)*(1-2*((y>>j)&1))) for j in range(n));right=(q//4)*(hp-h)+(q//2)*((z^zp)&y).bit_count();assert (left-right)%q==0
 checks+=1;return True
F.C.dense_check=exact
GG,om,dd,kk=F.omega(G,T,n)
target=sum((g[2]^h[2])<<(i*n) for i,(g,h) in enumerate(zip(comp,hc)));assert F.member(target,[o['image'] for o in om])
eq=[(sum(((o['image']>>j)&1)<<k for k,o in enumerate(om)),(target>>j)&1) for j in range(len(comp)*n)];eps=F.solve2(eq,len(om));assert eps is not None
ph=[Rational(0)]*n;dh=[0]*len(G);dl=[0]*len(G)
for k,o in enumerate(om):
 if (eps>>k)&1:ph=[a+b for a,b in zip(ph,o['phases'])];dh=[(a+b)%4 for a,b in zip(dh,o['betas'])];dl=[a^b for a,b in zip(dl,o['delta'])]
new=[((g[0]+h)%4,g[1],g[2]^(d>>n)) for g,h,d in zip(G,dh,dl)];q=math.lcm(4,*[int(x.q) for x in ph]);assert exact(G,new,n,q,[int(x*q) for x in ph])
assert all(g[1:]==h[1:] for g,h in zip(new,H))
peqs=[(g[2]|(g[1]<<n),((h[0]-g[0])%4)//2) for g,h in zip(new,H)];pauli=F.solve2(peqs,2*n);assert pauli is not None
new=[((h+2*((z|(x<<n))&pauli).bit_count())%4,x,z) for h,x,z in new];assert new==H
factors=F.factors(G,n);assert len(factors)==1
actualchange=F.rr([F.label(g,n) for g in G])!=F.rr([F.label(g,n) for g in H]);assert actualchange
r={'status':'PASS','n':n,'logical_qubits':2,'traced_original_qubits_zero_based':[6,7],'physical_factor_count':len(factors),'support_strings':len(A),'orbit_basis_size':len(om),'exact_preimages_checked':checks,'target_in_full_universal_phase_image':True,'target_changes_binary_stabilizer_space':actualchange,'recovered_phase_denominator':q,'exact_final_Pauli_sign_correction_checked':True,'elapsed_seconds':time.time()-start,'scope':'Coupled mixed stabilizer codes obtained by tracing two physical qubits from credited graph-state LU pair. No assertion that traced pair remains LC-inequivalent. This tests universal phase-image/preimage and exact sign correction, not a full 25-qubit exhaustive-frame oracle.','sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(HERE/'TRACED25-CHECK.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
