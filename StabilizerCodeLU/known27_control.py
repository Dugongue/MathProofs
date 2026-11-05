"""Exact 27-qubit generalized-complementation control; only 64 support strings."""
import pathlib,sys,itertools,json,time,math,hashlib
HERE=pathlib.Path(__file__).parent;sys.path.insert(0,str(HERE));import full_controls as F
from sympy import Rational
start=time.time();n=27;T=list(range(n));
from modular_kernel import kernel_generators
Q=1<<(2+n*(n+1).bit_length());F.snf=lambda M:kernel_generators(M,Q)
subs=[sum(1<<j for j in K) for k in [4,5] for K in itertools.combinations(range(6),k)]
D=[(0,0,s|(1<<(6+j))) for j,s in enumerate(subs)]
comp=[(0,(1<<i)|sum(1<<(6+j) for j,s in enumerate(subs) if (s>>i)&1),0) for i in range(6)]
G=D+comp;A=[y|sum(((s&y).bit_count()%2)<<(6+j) for j,s in enumerate(subs)) for y in range(64)]
K=F.rr([F.label(g,n)&~(((1<<n)-1)<<n) for g in G])
orig_data=F.data
F.data=lambda gs,t,nn:(D,comp,A,K) if nn==27 else orig_data(gs,t,nn)
checks=0
def exact_support_check(gs,hs,nn,q,phases):
    global checks
    assert nn==27 and gs==G and len(hs)==len(G)
    assert hs[:21]==D
    for h,x,z in hs:assert (h-(x&z).bit_count())%2==0
    for g,h in itertools.combinations(hs,2):assert ((g[1]&h[2]).bit_count()+(g[2]&h[1]).bit_count())%2==0
    for (h,x,z),(hp,xp,zp) in zip(gs,hs):
        assert x==xp
        for y in A:
            left=sum(phases[j]*(((x>>j)&1)*(1-2*((y>>j)&1))) for j in range(n))
            right=(q//4)*(hp-h)+(q//2)*((z^zp)&y).bit_count()
            assert (left-right)%q==0
    checks+=1;return True
F.C.dense_check=exact_support_check
GG,om,dd,kk=F.omega(G,T,n)
target=sum((((1<<6)-1)^(1<<i))<<(i*n) for i in range(6));assert F.member(target,[o['image'] for o in om])
eq=[(sum(((o['image']>>j)&1)<<k for k,o in enumerate(om)),(target>>j)&1) for j in range(6*n)]
eps=F.solve2(eq,len(om));assert eps is not None
ph=[Rational(0)]*n;dh=[0]*len(G);dl=[0]*len(G)
for k,o in enumerate(om):
    if (eps>>k)&1:ph=[a+b for a,b in zip(ph,o['phases'])];dh=[(a+b)%4 for a,b in zip(dh,o['betas'])];dl=[a^b for a,b in zip(dl,o['delta'])]
new=[((g[0]+h)%4,g[1],g[2]^(d>>n)) for g,h,d in zip(G,dh,dl)];q=math.lcm(4,*[int(x.q) for x in ph]);assert exact_support_check(G,new,n,q,[int(x*q) for x in ph])
assert all(new[21+i][2]==(((1<<6)-1)^(1<<i)) for i in range(6))
# An independent direct r=2 incidence witness: 10 pair overlaps and 6 triple overlaps.
pair_counts=[sum((s&k)==k for s in subs) for k in [sum(1<<j for j in J) for J in itertools.combinations(range(6),2)]]
triple_counts=[sum((s&k)==k for s in subs) for k in [sum(1<<j for j in J) for J in itertools.combinations(range(6),3)]]
assert set(pair_counts)=={10} and set(triple_counts)=={6}
r={'status':'PASS','n':n,'logical_qubits':0,'support_strings':64,'phase_orbit_basis_size':len(om),'exact_orbit_preimages_checked':checks,'inner_clique_target_in_full_phase_image':True,'pair_common_neighbors':10,'triple_common_neighbors':6,'returned_phase_denominator':q,'returned_turns':[str(x%1) for x in ph],'universal_phase_grid_bits':Q.bit_length()-1,'elapsed_seconds':time.time()-start,'scope':'Known 27-qubit 4/5-subset generalized-complementation construction, credited prior work. Tests new full orbit-image inclusion/preimages, not novelty or fresh LC-inequivalence proof. No Hilbert-space expansion.','sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(HERE/'KNOWN27-CHECK.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
