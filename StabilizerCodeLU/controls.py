"""Bounded exact controls; exhaustive small matrices, not a universal proof."""
import sys,pathlib,random,itertools,json,time,hashlib
HERE=pathlib.Path(__file__).parent
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form

def hnf(rows,d):
    if not rows:return []
    return [list(map(int,row)) for row in hermite_normal_form(Matrix(rows).T).T.tolist()]

def xor_basis(vs):
    b={}
    for v in vs:
        while v:
            j=v.bit_length()-1
            if j in b:v^=b[j]
            else:b[j]=v;break
    return list(b.values())

def translate(row,a,ell,n):
    return [(-v if (a>>j)&1 else v) for j,v in enumerate(row[:n])]+[row[n],-row[n+1] if (a&ell).bit_count()%2 else row[n+1]]

def orbit_compress(v0,abasis,ell,n):
    b=hnf([v0],n+2)
    for a in abasis:b=hnf(b+[translate(v,a,ell,n) for v in b],n+2)
    return b

def pmul(a,b):
    h,x,z=a;hh,xx,zz=b
    return ((h+hh+2*(z&xx).bit_count())%4,x^xx,z^zz)

def group(gens):
    out=[(0,0,0)]
    for g in gens:out += [pmul(h,g) for h in out]
    assert len(set((x,z) for h,x,z in out))==len(out)
    return out

def cliff(g,H=None,S=None,CX=None):
    h,x,z=g
    if H is not None:
        j=H;xb=(x>>j)&1;zb=(z>>j)&1;h=(h+2*xb*zb)%4
        if xb!=zb:x^=1<<j;z^=1<<j
    if S is not None:
        j=S;xb=(x>>j)&1;h=(h+xb)%4
        if xb:z^=1<<j
    if CX is not None:
        c,t=CX
        if (x>>c)&1:x^=1<<t
        if (z>>t)&1:z^=1<<c
    return h,x,z

def random_code(n,r,rng):
    gs=[(0,0,1<<j) for j in range(r)]
    for _ in range(4*n+3):
        op=rng.randrange(3);j=rng.randrange(n)
        kw={'H':j} if op==0 else {'S':j}
        if op==2 and n>1:
            t=rng.randrange(n-1);t+=t>=j;kw={'CX':(j,t)}
        gs=[cliff(g,**kw) for g in gs]
    return gs

def dense(gs,n,q):
    out={};G=group(gs)
    for y in range(1<<n):
        temp={}
        for h,x,z in G:
            phase=(h+2*(z&y).bit_count())%4;xy=(y^x,y)
            a,b=temp.get(xy,(0,0));a += [1,0,-1,0][phase];b += [0,1,0,-1][phase];temp[xy]=(a,b)
        for xy,(a,b) in temp.items():
            if not (a or b):continue
            assert not (a and b)
            phase=(0 if a>0 else 2) if a else (1 if b>0 else 3)
            out[xy]=(abs(a or b),phase*(q//4)%q)
    return out

def dense_check(gs,hs,n,q,phases):
    if len(gs)!=len(hs):return False
    a=dense(gs,n,q);b=dense(hs,n,q)
    if a.keys()!=b.keys():return False
    for (x,y),(mag,angle) in a.items():
        mm,aa=b[(x,y)]
        if mag!=mm:return False
        shift=sum(phases[j]*(((x>>j)&1)-((y>>j)&1)) for j in range(n))
        if (angle+shift-aa)%q:return False
    return True

def compressed_check(gs,hs,n,q,phases,check_lattice=False):
    G=group(gs);H=group(hs)
    dg={(h,z) for h,x,z in G if x==0};dh={(h,z) for h,x,z in H if x==0}
    if dg!=dh:return False
    cx={x for h,x,z in G};ch={x for h,x,z in H}
    if cx!=ch:return False
    A=[y for y in range(1<<n) if all((h+2*(z&y).bit_count())%4==0 for h,z in dg)]
    assert A
    y0=A[0];ab=xor_basis([y^y0 for y in A]);cb=xor_basis(cx)
    for c in cb:
        h,_,z=next(g for g in G if g[1]==c);hp,_,zp=next(g for g in H if g[1]==c)
        delta=(hp-h)%4;ell=z^zp
        def row(y):return [(1 if (c>>j)&1 else 0)*(-1 if (y>>j)&1 else 1) for j in range(n)]+[-(delta+1),-1 if (ell&y).bit_count()%2 else 1]
        B=orbit_compress(row(y0),ab,ell,n)
        if check_lattice:assert B==hnf([row(y) for y in A],n+2)
        for v in B:
            dot=4*sum(v[j]*phases[j] for j in range(n))+q*(v[n]+v[n+1])
            if dot%(4*q):return False
    return True

def run():
    t=time.time();rng=random.Random(20261104);generic=0;cases=0;positive=0;negative=0;multi=0
    for n in range(1,8):
        for _ in range(24):
            ab=xor_basis([rng.randrange(1<<n) for _ in range(rng.randrange(n+1))]);y0=rng.randrange(1<<n);ell=rng.randrange(1<<n);c=rng.randrange(1<<n);dh=rng.randrange(4)
            def row(y):return [((c>>j)&1)*(-1 if (y>>j)&1 else 1) for j in range(n)]+[-(dh+1),-1 if (ell&y).bit_count()%2 else 1]
            Y=[y0]
            for a in ab:Y += [y^a for y in Y]
            assert orbit_compress(row(y0),ab,ell,n)==hnf([row(y) for y in Y],n+2)
            generic+=1
    for n in range(1,7):
        for _ in range(35):
            r=rng.randrange(n+1);G=random_code(n,r,rng);H=list(G);q=rng.choice([4,8,12,20]);phases=[0]*n
            if rng.randrange(2):
                for j in range(n):
                    times=rng.randrange(4);phases[j]=(q//4)*times
                    for _ in range(times):H=[cliff(g,S=j) for g in H]
            else:
                phases=[rng.randrange(q) for j in range(n)]
                if rng.randrange(2):H=random_code(n,r,rng)
            a=dense_check(G,H,n,q,phases);b=compressed_check(G,H,n,q,phases,True);assert a==b,(G,H,n,q,phases,a,b)
            cases+=1;positive+=a;negative+=not a;multi+=n-r>=2
    # Exact non-Clifford cancellation on Bell and GHZ factors.
    for n,G,phases in [(2,[(0,3,0),(0,0,3)],[1,7]),(3,[(0,7,0),(0,0,3),(0,0,6)],[1,7,0]),(4,[(0,0,3)],[1,3,5,7])]:
        assert dense_check(G,G,n,8,phases);assert compressed_check(G,G,n,8,phases,True);cases+=1;positive+=1
    result={'status':'PASS','generic_signed_orbit_lattice_cases':generic,'exact_stabilizer_projector_comparisons':cases,'positive_transformations':positive,'negative_transformations':negative,'arbitrary_k_random_cases_with_k_at_least_2':multi,'max_physical_qubits':6,'phase_denominators':[4,8,12,20],'elapsed_seconds':time.time()-t,'meaning':'Bounded exact controls only. Dense projector and full-orbit enumeration appear only in test oracle, not the proposed polynomial algorithm.','controls_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
    (HERE/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8');print(json.dumps(result,indent=2))
if __name__=='__main__':run()
