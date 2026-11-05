import math,json
from fractions import Fraction
from pathlib import Path
cases=0; minimum=None
for m in range(0,9):
 for a in range(1,41):
  for b in range(1,41):
   if math.gcd(a,b)!=1:continue
   q=a*a+b*b-m*a*b
   if q>1:continue
   for u in range(a+1):
    for w in range(b+1):
     delta=b*u-a*w
     if delta<=0:continue
     z=b-w; D=m*u*z-u*(a-u)-w*z
     assert a*b*D==delta*(a*u+b*z)-q*u*z
     assert D>0
     cases+=1
     if minimum is None or D<minimum:minimum=D
# Explicit huge primitive reciprocal pair is not numerically reduced by gcd.
N=(1<<200)+39
alpha=(N,N+1);beta=(2*N-1,N)
assert math.gcd(*alpha)==math.gcd(*beta)==1
assert alpha[0]*beta[0]+alpha[1]*beta[1]-3*alpha[0]*beta[1]==0
result={'status':'PASS_FINITE_IDENTITY_CONTROLS','incidence_pairs':cases,'m_range':[0,8],'a_b_range':[1,40],'minimum_codimension':minimum,'huge_core_input_bits':N.bit_length(),'purpose':'Exact incidence algebra/inequality and primitive-size sanity check; does not certify universal algorithm or novelty.'}
Path(__file__).with_name('CONTROLS.json').write_text(json.dumps(result,indent=2),encoding='utf8');print(json.dumps(result))
