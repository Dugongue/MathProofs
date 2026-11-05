"""Exact source-moment checks; the parity argument is proved in SHARPNESS.txt."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib,json

def controls(n,kind):
    def xx(i,a,j,b):
        if kind!='nonsymmetric':return Q(0)
        pair=tuple(sorted(((i,a),(j,b))))
        if pair==((0,0),(1,1)):return Q(5,3)
        if pair==((0,1),(1,0)):return Q(1,3)
        return Q(0)
    def xy(i,a,b,j):
        if kind=='identity':return Q(int(i==a==b==j))
        if max(i,a,b,j)<2:return Q(int(i==j and a==b),2)
        return Q(int(i==a==b==j and i>=2))
    A=[[0]*n for _ in range(n)];B=[[0]*n for _ in range(n)]
    if kind=='identity':
        for i in range(n):A[i][i]=1
    else:A[0][1]=B[0][1]=1;A[1][0]=-2;B[1][0]=-3
    checks=0
    for i in range(n):
        for j in range(n):
            congr=sum(Q(A[a][b])*xx(i,a,j,b) for a in range(n) for b in range(n))-B[i][j]
            forward=sum(xy(i,k,k,j) for k in range(n))-int(i==j)
            reverse=sum(xy(k,j,i,k) for k in range(n))-int(i==j)
            assert congr==forward==reverse==0,(n,kind,i,j,congr,forward,reverse)
            checks+=3
    return {'n':n,'kind':kind,'rational_source_moment_checks':checks,'all_source_expectations_zero':True,'L_one':1}

if __name__=='__main__':
    p=Path(__file__).parent
    cases=[controls(n,'identity') for n in range(1,21)]
    cases += [controls(n,'nonsymmetric') for n in range(2,21)]
    out={'status':'PASS_EXACT_RATIONAL_MOMENT_CONTROLS','proof_sha256':hashlib.sha256((p/'CONGRUENCE-SHARPNESS.md').read_bytes()).hexdigest(),'cases':cases,'total_source_moment_checks':sum(c['rational_source_moment_checks'] for c in cases),'scope':'Finite exact moments corroborate uniform formulas; parity lower-bound proof remains mathematical, not inferred from controls.'}
    (p/'SHARPNESS-CONTROLS.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(out['status'],out['total_source_moment_checks'])
