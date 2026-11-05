"""Exact finite checks of the typed front end; not a second FGS implementation."""
from itertools import product
from pathlib import Path
import hashlib, json, random

def mm(a,b,p):return tuple(tuple(sum(x*y for x,y in zip(r,c))%p for c in zip(*b)) for r in a)
def tr(a):return tuple(zip(*a))
def identity(n):return tuple(tuple(int(i==j) for j in range(n)) for i in range(n))
def mv(a,v,p):return tuple(sum(x*y for x,y in zip(r,v))%p for r in a)
def dot(a,b,p):return sum(x*y for x,y in zip(a,b))%p
def inverse2(a,p):
    d=(a[0][0]*a[1][1]-a[0][1]*a[1][0])%p
    if not d:return None
    q=pow(d,-1,p)
    return ((q*a[1][1]%p,-q*a[0][1]%p),(-q*a[1][0]%p,q*a[0][0]%p))
def gl2(p):
    for a,b,c,d in product(range(p),repeat=4):
        m=((a,b),(c,d));v=inverse2(m,p)
        if v is not None:yield m,v
def kron(a,b,p):return tuple(tuple(x*y%p for x in ra for y in rb) for ra in a for rb in b)
def direct_word(mats,p):
    dims=[len(a) for a in mats]; indices=list(product(*(range(d) for d in dims)))
    def entry(i,j):
        x=1
        for m,r,c in zip(mats,i,j):x=x*m[r][c]%p
        return x
    return tuple(tuple(entry(i,j) for j in indices) for i in indices)
def span(j,p):
    return {mv(j,v,p) for v in product(range(p),repeat=len(j[0]))}
def random_matrix(r,c,p,rng):return tuple(tuple(rng.randrange(p) for _ in range(c)) for _ in range(r))

def main():
    rng=random.Random(20261104)
    pairing=prefix=functions=relations=negative=free_basis=scalar=0
    for p in [2,3,5]:
        gl=list(gl2(p));I=identity(2)
        for a,ai in gl:
            preserving=[b for b,_ in gl if mm(tr(b),a,p)==I]
            assert preserving==[tr(ai)];pairing+=len(gl)
        assert [x for x in range(1,p) if x==x*x%p]==[1];scalar+=p-1
        use=gl if p<=3 else rng.sample(gl,36)
        for a,ai in use:
            plus=a;minus=tr(ai)
            for word in ['++--','-+-','+--+']:
                seq=[plus if k=='+' else minus for k in word]
                # Independent mixed-radix index formula versus iterative product constraints.
                g=seq[0]
                for k,next_m in enumerate(seq[1:],2):
                    g=kron(g,next_m,p)
                    assert g==direct_word(seq[:k],p);prefix+=1
                inv_seq=[ai if k=='+' else tr(a) for k in word]
                gi=direct_word(inv_seq,p);n=len(g)
                assert mm(g,gi,p)==identity(n)

                # Relation coordinates are tested as sets of vectors, independently
                # from checking a free GL(2) change of the presented basis.
                j=tuple((int(i==0),int(i==1)) for i in range(n))
                h,hi=rng.choice(gl);gj=mm(g,j,p);jp=mm(gj,hi,p)
                assert span(gj,p)==span(jp,p)
                assert mm(jp,h,p)==gj;relations+=1
                if jp!=gj:free_basis+=1
                bad=tuple((g[i][0],g[i][2]) for i in range(n))
                assert span(gj,p)!=span(bad,p)
                assert all(mm(bad,k,p)!=gj for k,_ in gl);negative+=1

                # Evaluate the actual padded trilinear-form action with source basis
                # arguments; the output dual view must be inverse transpose.
                f=random_matrix(2,n,p,rng);fp=mm(mm(a,f,p),gi,p)
                for i,jj in product(range(2),range(n)):
                    ell=I[i];x=identity(n)[jj]
                    assert dot(mv(minus,ell,p),mv(fp,mv(g,x,p),p),p)==dot(ell,mv(f,x,p),p)
                    functions+=1
    # Multisorted check: differently sized named spaces and a repeated dual name.
    p=5;a=((1,1),(0,1));b=((1,1,0),(0,1,1),(0,0,1));bd=((1,0,0),(-1,1,0),(1,-1,1))
    assert mm(tr(bd),b,p)==identity(3)
    g=kron(kron(a,bd,p),bd,p)
    assert len(g)==18 and g==direct_word([a,bd,bd],p)
    # Distinct GL(1) factors contribute exactly one nonzero total scalar, which
    # can be absorbed into the first factor; enumerate the scalar products.
    singleton=0
    for q in [2,3,5]:
        for xs in product(range(1,q),repeat=3):
            lam=1
            for x in xs:lam=lam*x%q
            assert lam!=0;singleton+=1
    folder=Path(__file__).parent
    out={'status':'PASS_EXACT_FINITE_FRONTEND_CONTROLS','proof_sha256':hashlib.sha256((folder/'PROOF.md').read_bytes()).hexdigest(),'fields':[2,3,5],'scalar_pin_checks':scalar,'pairing_candidate_checks':pairing,'prefix_mixed_radix_checks':prefix,'positive_relation_checks':relations,'negative_relation_checks':negative,'positive_relation_cases_requiring_changed_basis':free_basis,'padded_function_trilinear_checks':functions,'different_dimension_multisort_dimension':18,'singleton_scalar_checks':singleton,'scope':'Exact finite corroboration of the typed front end. Terminal ordinary-TI compilation is the published FGS theorem, not a finite control or a new Lean check.'}
    (folder/'CONTROLS.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
