"""Second rigorous positivity replay, using rational congruence and Gershgorin."""
import sys,json,hashlib,argparse
from pathlib import Path
if not __debug__:raise RuntimeError('Do not use Python optimization flags.')
p=argparse.ArgumentParser();p.add_argument('--deps');p.add_argument('--receipt');args=p.parse_args()
if args.deps:sys.path.insert(0,args.deps)
from flint import arb,arb_mat,fmpq,ctx
root=Path(__file__).parent;data=(root/'FourOutcomeTriple_UniversalSOSCertificate.json').read_bytes();cert=json.loads(data);witness=json.loads((root/'whitening-witness.json').read_text())
assert hashlib.sha256(data).hexdigest()==witness['certificate_sha256']
ctx.prec=384;c=(arb.pi()/9).cos()
def val(v):return arb(fmpq(v[0]))+arb(fmpq(v[1]))*c+arb(fmpq(v[2]))*c*c
result={'certificate_sha256':witness['certificate_sha256'],'method':'rational congruence and rigorous interval Gershgorin','precision_bits':384}
for name,key in [('parent','parent_gram'),('marginal_contact','marginal_free_principal')]:
 record=witness[name];M=cert[key];n=len(M);assert all(M[i][j]==M[j][i] for i in range(n) for j in range(n))
 den=record['whitening_denominator'];H=record['whitening_integer_matrix'];assert len(H)==n and all(len(r)==n for r in H)
 A=arb_mat([[val(x) for x in row] for row in M]);Q=arb_mat([[arb(int(x))/den for x in row] for row in H]);V=Q*A*Q.transpose()
 margins=[]
 for i in range(n):
  lower=V[i,i]-sum((abs(V[i,j]) for j in range(n) if j!=i),arb(0));assert lower>arb(fmpq(99,100)),(name,i,lower);margins.append(str(lower))
 result[name]={'dimension':n,'every_rigorous_margin_greater_than':'99/100'}
 print('RIGOROUS GERSHGORIN PASS',name,n,'all margins > 99/100',flush=True)
if args.receipt:Path(args.receipt).write_text(json.dumps(result,indent=2))
print('SECOND POSITIVITY AUDIT PASSED')
