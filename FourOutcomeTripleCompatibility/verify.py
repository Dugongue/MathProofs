"""Independent full-word identity and positive-Gram audit of the sharp certificate."""
import sys,json,time,hashlib
from pathlib import Path
from fractions import Fraction as F
from itertools import permutations
import argparse
parser=argparse.ArgumentParser(description='Replay the exact universal four-outcome triple certificate.')
parser.add_argument('--deps',help='Optional local Python dependency directory.')
parser.add_argument('--receipt',help='Optional path for a fresh verification receipt.')
args=parser.parse_args()
if args.deps:sys.path.insert(0,args.deps)
if not __debug__:raise RuntimeError('Do not run this checker with Python optimization flags.')
import audit_primitives as a
from flint import arb,fmpq,fmpq_mat,ctx
base=Path(__file__).parent
source=base/'FourOutcomeTriple_UniversalSOSCertificate.json'
start=time.time();cert=json.loads(source.read_text())
Z=[[a.field(x) for x in row] for row in cert['parent_gram']]
assert cert['words']==[list(w) for w in a.WORDS]
assert all(Z[i][j]==Z[j][i] for i in range(9) for j in range(9))
labels=[tuple(x) for x in cert['labels']]
label_index={x:i for i,x in enumerate(labels)}
for perm in permutations(range(3)):
    action=[label_index[tuple(perm[x] for x in label)] for label in labels]
    assert all(Z[action[i]][action[j]]==Z[i][j] for i in range(9) for j in range(9))
print('EXACT PARENT SETTING-PERMUTATION SYMMETRY VERIFIED',flush=True)
Y=[[None]*170 for _ in range(170)]
for orb,x in zip(cert['marginal_orbits'],cert['marginal_orbit_coefficients']):
    v=a.field(x)
    for i,j in orb:
        assert Y[i][j] is None
        Y[i][j]=Y[j][i]=v
assert all(x is not None for row in Y for x in row)
print('Loaded exact matrices; seconds',time.time()-start,flush=True)
p=a.marginal_from_parent(Z)
q=a.marginal_from_word_gram(Y)
r=a.padd(p,a.pscale(q,-1))
assert not r,(len(r),next(iter(r.items())))
print('FULL UNCOLLAPSED EXACT MARGINAL IDENTITY VERIFIED',len(p),'words; seconds',time.time()-start,flush=True)

# Normalization uses explicit setting labels, never identifying different settings.
amps=a.parent_amplitudes();generic={}
for i,p0 in enumerate(amps):
    for j,q0 in enumerate(amps):
        z=Z[i][j]
        if z==a.ZERO:continue
        for u,x in p0.items():
            for v,y in q0.items():
                w=tuple(reversed(u))+v
                generic[w]=a.add(generic.get(w,a.ZERO),a.mul(z,a.mul(x,y)))

def collapse_repeats(w):return tuple(x for i,x in enumerate(w) if i==0 or w[i-1]!=x)

def sum_word(w):
    factor=4**(3-len(set(w)))
    w=collapse_repeats(w)
    while True:
        singleton=next((x for x in set(w) if w.count(x)==1),None)
        if singleton is None:return w,factor
        w=collapse_repeats(tuple(x for x in w if x!=singleton))

norm={}
for w,x in generic.items():
    w,m=sum_word(w)
    norm[w]=a.add(norm.get(w,a.ZERO),a.scale(x,m))
norm[()]=a.sub(norm.get((),a.ZERO),a.ONE)
assert all(x==a.ZERO for x in norm.values()),norm
print('EXACT UNIVERSAL NORMALIZATION VERIFIED; seconds',time.time()-start,flush=True)

# Recover the exact contact factorization using all matrix entries.
B=fmpq_mat([[fmpq(x) for x in row] for row in cert['contact_basis']])
W=[[a.field(x) for x in row] for row in cert['marginal_free_principal']]
free=cert['contact_free_rows']
assert len(free)==106 and len(set(free))==106
assert all(Y[free[i]][free[j]]==W[i][j] for i in range(106) for j in range(106))
for k in range(3):
    wk=fmpq_mat([[fmpq(str(x[k])) for x in row] for row in W])
    yk=fmpq_mat([[fmpq(str(x[k])) for x in row] for row in Y])
    assert B*wk*B.transpose()==yk
print('EXACT FULL CONTACT FACTORIZATION VERIFIED; seconds',time.time()-start,flush=True)

# Independent interval LDL via the original-entry recurrence, rather than in-place Schur updates.
ctx.prec=384
c=(arb.pi()/9).cos()
assert c>arb(fmpq(93969,100000)) and c<arb(fmpq(93970,100000))
assert (8*c*c*c-6*c-1).contains(0)

def val(x):return arb(fmpq(str(x[0])))+arb(fmpq(str(x[1])))*c+arb(fmpq(str(x[2])))*c*c

def positive_ldl(matrix,name):
    n=len(matrix);A=[[val(x) for x in row] for row in matrix]
    L=[[arb(0) for j in range(n)] for i in range(n)]
    d=[]
    for k in range(n):
        pivot=A[k][k]-sum((L[k][r]*L[k][r]*d[r] for r in range(k)),arb(0))
        assert pivot>0,(name,k,str(pivot))
        d.append(pivot);L[k][k]=arb(1)
        for i in range(k+1,n):
            L[i][k]=(A[i][k]-sum((L[i][r]*L[k][r]*d[r] for r in range(k)),arb(0)))/pivot
    print('RIGOROUS POSITIVE LDL',name,n,'last',d[-1],'seconds',time.time()-start,flush=True)
    return [str(x) for x in d]

zp=positive_ldl(Z,'parent9')
wp=positive_ldl(W,'marginal106')
receipt={'certificate_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
    'audit_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    'algebra_primitives_sha256':hashlib.sha256((base/'audit_primitives.py').read_bytes()).hexdigest(),
    'uncollapsed_exact_marginal_identity':True,'nonzero_marginal_words':len(p),
    'exact_universal_normalization':True,'exact_parent_setting_symmetry':True,'exact_contact_factorization':True,
    'parent_positive_definite':True,'contact_gram_positive_definite':True,
    'interval_precision_bits':384,'parent_ldl_pivots':zp,'marginal_ldl_pivots':wp,
    'elapsed_seconds':time.time()-start,'lean_claim':False}
if args.receipt:Path(args.receipt).write_text(json.dumps(receipt,indent=2))
print('INDEPENDENT AUDIT PASSED',receipt['certificate_sha256'],flush=True)
