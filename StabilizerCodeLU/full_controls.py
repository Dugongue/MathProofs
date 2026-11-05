"""Small exact FULL-algorithm controls. Group enumeration is a bounded test convenience."""
import sys,pathlib,itertools,random,json,time,hashlib,math
HERE=pathlib.Path(__file__).parent
sys.path.insert(0,str(HERE))
import controls as C
from sympy import Matrix,Rational,ZZ
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.normalforms import smith_normal_decomp

def snf(M):
    D,U,V=smith_normal_decomp(DomainMatrix.from_Matrix(M).convert_to(ZZ))
    return D.to_Matrix(),U.to_Matrix(),V.to_Matrix()
def label(g,n):return g[1]|(g[2]<<n)
def support(g):return g[1]|g[2]
def basis_gens(gs,n):
    b={};out=[]
    for g in gs:
        v=label(g,n)
        while v:
            j=v.bit_length()-1
            if j in b:v^=b[j]
            else:b[j]=v;out.append(g);break
    return out

def rr(vs):
    b={}
    for v in vs:
        for j in sorted(b,reverse=True):
            if (v>>j)&1:v^=b[j]
        if v:
            j=v.bit_length()-1
            for k in list(b):
                if (b[k]>>j)&1:b[k]^=v
            b[j]=v
    return [b[j] for j in sorted(b,reverse=True)]
def member(v,vs):
    for b in rr(vs):
        if (v>>(b.bit_length()-1))&1:v^=b
    return v==0

def solve2(eqs,N):
    b={}
    for v,rhs in eqs:
        for j in sorted(b,reverse=True):
            if (v>>j)&1:v^=b[j][0];rhs^=b[j][1]
        if not v:
            if rhs:return None
            continue
        j=v.bit_length()-1;b[j]=(v,rhs)
    ans=0
    for j in sorted(b):
        v,rhs=b[j]
        if (v&ans).bit_count()%2 != rhs:ans|=1<<j
    assert all((a&ans).bit_count()%2==b for a,b in eqs)
    return ans

def perp(vs,N):
    r=rr(vs);piv={v.bit_length()-1 for v in r};out=[]
    for f in range(N):
        if f in piv:continue
        x=1<<f
        for v in reversed(r):
            j=v.bit_length()-1
            if (v&x).bit_count()%2:x|=1<<j
        assert all((v&x).bit_count()%2==0 for v in vs)
        out.append(x)
    return out

def factors(gs,n):
    parent=list(range(n))
    def find(a):
        while parent[a]!=a:parent[a]=parent[parent[a]];a=parent[a]
        return a
    for v in rr([label(g,n) for g in gs]):
        supp=(v&((1<<n)-1))|(v>>n);J=[j for j in range(n) if (supp>>j)&1]
        for j in J[1:]:parent[find(j)]=find(J[0])
    return sorted([tuple(j for j in range(n) if find(j)==r) for r in {find(j) for j in range(n)}])

def subgroup(gs,J,n):
    mask=sum(1<<j for j in J);G=[g for g in C.group(gs) if not support(g)&~mask];out=[]
    for h,x,z in basis_gens(G,n):out.append((h,sum(((x>>j)&1)<<k for k,j in enumerate(J)),sum(((z>>j)&1)<<k for k,j in enumerate(J))))
    return out

def axes(gs,hs,n):
    G=C.group(gs);H=C.group(hs);T=[];source=list(gs);target=list(hs)
    for i in range(n):
        J=(1<<n)-1
        def feasible(G,J):return any(not support(g)&~J and (((g[1]>>i)&1) or ((g[2]>>i)&1)) for g in G)
        if not feasible(G,J):return None
        for j in range(n):
            if j!=i and feasible(G,J&~(1<<j)):J&=~(1<<j)
        def projection(G):return {( ((x>>i)&1)|(((z>>i)&1)<<1)) for h,x,z in G if not (x|z)&~J}
        a=projection(G);b=projection(H)
        if len(a)!=len(b):return None
        if len(a)==2:
            T.append(i)
            for code,axis in [(source,next(x for x in a if x)),(target,next(x for x in b if x))]:
                if axis==1:
                    for k in range(len(code)):code[k]=C.cliff(code[k],H=i)
                elif axis==3:
                    for _ in range(3):
                        for k in range(len(code)):code[k]=C.cliff(code[k],S=i)
                    for k in range(len(code)):code[k]=C.cliff(code[k],H=i)
    return source,target,T,[j for j in range(n) if j not in T]

def data(gs,T,n):
    G=C.group(gs);tm=sum(1<<j for j in T);D=basis_gens([g for g in G if not g[1]&tm],n)
    cb={};comp=[]
    for g in G:
        v=sum(((g[1]>>j)&1)<<k for k,j in enumerate(T))
        for k in sorted(cb,reverse=True):
            if (v>>k)&1:v^=cb[k]
        if v:cb[v.bit_length()-1]=v;comp.append(g)
    dz=[g for g in G if not g[1]]
    A=[y for y in range(1<<n) if all((h+2*(z&y).bit_count())%4==0 for h,x,z in dz)]
    assert A
    K=rr([label(g,n)&~(tm<<n) for g in G]);return D,comp,A,K

def omega(gs,T,n):
    D,comp,A,K=data(gs,T,n);t=len(T);a=len(comp)
    if not a:return D+comp,[],D,K
    N=t+a*t+a;rows=[]
    Y=sorted({sum(((y>>j)&1)<<k for k,j in enumerate(T)) for y in A});y0=Y[0];AB=C.xor_basis([y^y0 for y in Y])
    for i,g in enumerate(comp):
        c=sum(((g[1]>>j)&1)<<k for k,j in enumerate(T))
        r=[((c>>j)&1)*(-1 if (y0>>j)&1 else 1) for j in range(t)]+[-((y0>>j)&1) for j in range(t)]+[-1]
        B=C.hnf([r],2*t+1)
        def move(v,b):return [(-v[j] if (b>>j)&1 else v[j]) for j in range(t)]+[((-v[t+j]+v[-1]) if (b>>j)&1 else v[t+j]) for j in range(t)]+[v[-1]]
        for b in AB:B=C.hnf(B+[move(v,b) for v in B],2*t+1)
        for v in B:
            row=[0]*N;row[:t]=v[:t];row[t+i*t:t+(i+1)*t]=v[t:2*t];row[t+a*t+i]=v[-1];rows.append(row)
    for j in range(a*t):r=[0]*N;r[t+j]=2;rows.append(r)
    for j in range(a):r=[0]*N;r[t+a*t+j]=4;rows.append(r)
    DD,U,V=snf(Matrix(rows));images=[];basis=[]
    for j in range(min(DD.rows,DD.cols)):
        dj=abs(int(DD[j,j]))
        if not dj:continue
        v=[Rational(V[k,j],dj)%1 for k in range(N)];im=0
        for k in range(a*t):
            z=2*v[t+k];assert z.q==1
            if int(z)%2:im|=1<<k
        if not im or member(im,images):continue
        delta=[0]*len(D)
        for i in range(a):delta.append(sum(((im>>(i*t+k))&1)<<(n+q) for k,q in enumerate(T)))
        phases=[Rational(0)]*n
        for k,q in enumerate(T):phases[q]=v[k]
        betas=[0]*len(D)+[int(4*v[t+a*t+i])%4 for i in range(a)]
        item={'image':im,'delta':delta,'phases':phases,'betas':betas};images.append(im);basis.append(item)
        new=[((g[0]+dh)%4,g[1],g[2]^(dl>>n)) for g,dh,dl in zip(D+comp,betas,delta)]
        q=math.lcm(4,*[int(x.q) for x in phases]);assert C.dense_check(D+comp,new,n,q,[int(x*q) for x in phases])
    for j in range(min(DD.rows,DD.cols),N):assert all(V[t+k,j]==0 for k in range(a*t))
    return D+comp,basis,D,K

# Six unsigned single-qubit Clifford matrices with exact H/S lifts.
def cliffords():
    out={};queue=[([],[(0,1,0),(0,0,1)])]
    while queue:
        word,gs=queue.pop(0);key=tuple((g[1],g[2]) for g in gs)
        if key in out:continue
        out[key]=word
        for letter in ['H','S']:queue.append((word+[letter],[C.cliff(g,**{letter:0}) for g in gs]))
    assert len(out)==6
    return out
CLIFF=cliffords()
def apply_local(gs,j,word):
    for l in word:gs=[C.cliff(g,**{l:j}) for g in gs]
    return gs

def matching(gs,hs,n,T,W,orbit=None):
    gg,om,D,K=omega(gs,T,n) if orbit is None else orbit
    Dp,_,_,Kp=data(hs,T,n);S=rr([label(g,n) for g in gg]);Sp=rr([label(g,n) for g in hs])
    dv=[label(g,n) for g in D];dp=[label(g,n) for g in Dp]
    N=4*len(W)+len(om);tm=sum(1<<j for j in T);eq=[]
    def transform(v,adj=False):
        const=v&(tm|(tm<<n));parts=[0]*N
        for k,j in enumerate(W):
            x=(v>>j)&1;z=(v>>(n+j))&1
            maps=[x<<j,x<<(n+j),z<<j,z<<(n+j)]
            if adj:maps=[maps[3],maps[1],maps[2],maps[0]]
            parts[4*k:4*k+4]=maps
        return const,parts
    def contain(src,dst,adj=False,corrections=None):
        check=perp(dst,2*n)
        for i,v in enumerate(src):
            con,parts=transform(v,adj)
            if corrections is not None:
                for k,o in enumerate(om):parts[4*len(W)+k]=o['delta'][i]
            for h in check:
                mask=sum(((h&p).bit_count()%2)<<k for k,p in enumerate(parts));rhs=(h&con).bit_count()%2;eq.append((mask,rhs))
    contain([label(g,n) for g in gg],Sp,corrections=True)
    contain(dv,dp);contain(dp,dv,True);contain(K,Kp);contain(Kp,K,True)
    branches=[[]]
    if not T:
        branches=[]
        for key in CLIFF:
            a,b=key[0];c,d=key[1];branches.append([(1<<k,v) for k,v in enumerate([a,b,c,d])])
    ans=None
    for extra in branches:
        ans=solve2(eq+extra,N)
        if ans is not None:break
    if ans is None:return False
    words=[]
    for k,j in enumerate(W):
        a,b,c,d=[(ans>>(4*k+l))&1 for l in range(4)];assert (a*d+b*c)%2==1,(gs,hs,T,W,ans)
        words.append((j,CLIFF[((a,b),(c,d))]))
    delta=[0]*len(gg);betas=[0]*len(gg);phases=[Rational(0)]*n
    for k,o in enumerate(om):
        if (ans>>(4*len(W)+k))&1:
            delta=[a^b for a,b in zip(delta,o['delta'])];betas=[(a+b)%4 for a,b in zip(betas,o['betas'])];phases=[a+b for a,b in zip(phases,o['phases'])]
    new=[((g[0]+dh)%4,g[1],g[2]^(dl>>n)) for g,dh,dl in zip(gg,betas,delta)]
    q=math.lcm(4,*[int(x.q) for x in phases]);assert C.dense_check(gg,new,n,q,[int(x*q) for x in phases])
    for j,word in words:new=apply_local(new,j,word)
    assert rr([label(g,n) for g in new])==Sp
    H={label(g,n):g[0] for g in C.group(hs)};peqs=[]
    for h,x,z in new:
        diff=(H[x|(z<<n)]-h)%4;assert diff%2==0
        peqs.append((z|(x<<n),diff//2))
    pauli=solve2(peqs,2*n);assert pauli is not None
    new=[((h+2*((z|(x<<n))&pauli).bit_count())%4,x,z) for h,x,z in new]
    assert set(C.group(new))==set(C.group(hs))
    return True

def full(gs,hs,n,oracle=False):
    fs=factors(gs,n);ft=factors(hs,n)
    if fs!=ft:return False
    for J in fs:
        G=subgroup(gs,J,n);H=subgroup(hs,J,n);m=len(J)
        if len(G)!=len(H):return False
        if m<=1:continue
        if m==2 and len(G)==2:continue
        ax=axes(G,H,m)
        if ax is None:return False
        G,H,T,W=ax
        ok=oracle_factor(G,H,m,T,W) if oracle else matching(G,H,m,T,W)
        if not ok:return False
    return True

# Independent direct full-y torus oracle, enumerating all remaining Clifford blocks.
def torus_feasible(A,b,N):
    if not A:return True
    DD,U,V=snf(Matrix(A));rhs=U*Matrix(b)
    return all(rhs[i].q==1 for i in range(DD.rows) if i>=DD.cols or DD[i,i]==0)

def diagonal_unsigned(gs,hs,n,T):
    D,comp,A,K=data(gs,T,n);Dp,_,_,Kp=data(hs,T,n)
    if rr([label(g,n) for g in D])!=rr([label(g,n) for g in Dp]) or K!=Kp:return False
    tm=sum(1<<j for j in T);Hp={label(g,n)&~(tm<<n):g for g in C.group(hs)};a=len(comp);t=len(T)
    rows=[];rhs=[]
    for i,g in enumerate(comp):
        h,x,z=g;hp,xp,zp=Hp[label(g,n)&~(tm<<n)];assert x==xp
        ell=z^zp;assert not ell&~tm
        # Unknown beta_i is constrained to have Hermitian parity; signs remain free.
        for y in A:
            r=[((x>>j)&1)*(-1 if (y>>j)&1 else 1) for j in T]+[0]*a;r[t+i]=-1;rows.append(r);rhs.append(Rational((ell&y).bit_count(),2)%1)
        r=[0]*(t+a);r[t+i]=2;rows.append(r);rhs.append(Rational((ell&x).bit_count(),2)%1)
    return torus_feasible(rows,rhs,t+a)

def oracle_factor(gs,hs,n,T,W):
    for keys in itertools.product(CLIFF,repeat=len(W)):
        H=list(hs)
        # All six are closed under inverse, so forward enumeration suffices.
        for j,key in zip(W,keys):H=apply_local(H,j,CLIFF[key])
        if diagonal_unsigned(gs,H,n,T):return True
    return False

def run():
    start=time.time();rng=random.Random(20261105);rows=[];omega_cases=0
    # Arbitrary T subsets separately stress phase-image validity including k>1.
    for n in range(1,7):
        for _ in range(12):
            r=rng.randrange(n+1);G=C.random_code(n,r,rng);T=[j for j in range(n) if rng.randrange(2)]
            gg,om,D,K=omega(G,T,n);omega_cases+=1
            if len(om)<=7:
                for eps in range(1<<len(om)):
                    delta=[0]*len(gg);betas=[0]*len(gg);phases=[Rational(0)]*n
                    for k,o in enumerate(om):
                        if (eps>>k)&1:
                            delta=[a^b for a,b in zip(delta,o['delta'])];betas=[(a+b)%4 for a,b in zip(betas,o['betas'])];phases=[a+b for a,b in zip(phases,o['phases'])]
                    new=[((g[0]+dh)%4,g[1],g[2]^(dl>>n)) for g,dh,dl in zip(gg,betas,delta)]
                    q=math.lcm(4,*[int(x.q) for x in phases]);assert C.dense_check(gg,new,n,q,[int(x*q) for x in phases])
    for n in range(2,7):
        for _ in range(28):
            r=rng.randrange(n+1);G=C.random_code(n,r,rng)
            if rng.randrange(2):
                H=list(G)
                for j in range(n):H=apply_local(H,j,CLIFF[rng.choice(list(CLIFF))])
            else:H=C.random_code(n,r,rng)
            x=full(G,H,n);y=full(G,H,n,True);assert x==y,(G,H,n,x,y)
            rows.append({'n':n,'k':n-r,'accepted':x})
    # Indecomposable all-Clifford [[4,2,2]] and nontrivial full matching branches.
    for G in [[(0,15,0),(0,0,15)],[(0,7,0),(0,0,3),(0,0,6)],[(0,3,0),(0,0,3),(0,4,0)]]:
        n=max(support(g).bit_length() for g in G);H=list(G)
        for j in range(n):H=apply_local(H,j,CLIFF[rng.choice(list(CLIFF))])
        assert full(G,H,n) and full(G,H,n,True);rows.append({'n':n,'k':n-len(G),'accepted':True,'special':True})
    result={'status':'PASS','phase_orbit_systems':omega_cases,'full_algorithm_vs_exhaustive_Clifford_and_full_y_torus_cases':len(rows),'accepts':sum(x['accepted'] for x in rows),'rejects':sum(not x['accepted'] for x in rows),'arbitrary_k_cases_k_at_least_2':sum(x['k']>=2 for x in rows),'max_n':6,'elapsed_seconds':time.time()-start,'scope':'Exact small controls. Pauli-group/full-y enumeration occurs only as bounded test convenience/oracle, not the polynomial theorem algorithm.','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),'cases':rows}
    (HERE/'FULL-CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
if __name__=='__main__':run()
