"""Exact finite diagnostics for determinant assembly, not an oracle implementation."""
from itertools import combinations,product
from pathlib import Path
import hashlib,json,random

HERE=Path(__file__).resolve().parent

def det(a,q):return (a[0]*a[3]-a[1]*a[2])%q
def gl2(q):return [a for a in product(range(q),repeat=4) if det(a,q)]

def mode(t,a,k,q):
    out=[]
    for i in product(range(2),repeat=3):
        v=0
        for j in range(2):
            p=list(i);p[k]=j
            v+=a[2*i[k]+j]*t[4*p[0]+2*p[1]+p[2]]
        out.append(v%q)
    return tuple(out)

def diagonal(weights):return (weights[0],0,0,0,0,0,0,weights[1])
def action(t,ms,q):
    for k,a in enumerate(ms):t=mode(t,a,k,q)
    return t

def exhaustive_determinants(t,s,gl,q):
    """Enumerate A,B; solve the full C equations uniquely on concise tensors."""
    answer=set();found=0
    for a in gl:
        ta=mode(t,a,0,q)
        for b in gl:
            u=mode(ta,b,1,q)
            for r,z in combinations(range(4),2):
                x,y=u[2*r:2*r+2];w,v=u[2*z:2*z+2]
                d=(x*v-y*w)%q
                if d:break
            else:raise AssertionError('third flattening must have rank 2')
            inv=pow(d,-1,q);c=[]
            for k in range(2):
                c.extend(((s[2*r+k]*v-y*s[2*z+k])*inv%q,
                          (x*s[2*z+k]-s[2*r+k]*w)*inv%q))
            if det(c,q) and mode(u,c,2,q)==s:
                answer.add((det(a,q),det(b,q),det(c,q)));found+=1
    return answer,found

def expected_direct_sum(source,target,s_basis,t_basis,q):
    unit=tuple(product(range(1,q),repeat=3))
    def prod3(a,b):return tuple(x*y%q for x,y in zip(a,b))
    cosets=[]
    for a,b in zip(source,target):
        r=b*pow(a,-1,q)%q
        cosets.append({u for u in unit if u[0]*u[1]*u[2]%q==r})
    c=tuple(det(b,q)*pow(det(a,q),-1,q)%q for a,b in zip(t_basis,s_basis))
    ref={prod3(c,prod3(u,v)) for u in cosets[0] for v in cosets[1]}
    return ref|{prod3((q-1,)*3,u) for u in ref},ref

def fixed_algebra_control():
    # F3[epsilon]/epsilon^2 x F9 x F3; in F9 use u^2=-1.
    one=(1,0,1,0,1);zero=(0,0,0,0,0);q=3
    def sub(a,b):return tuple((x-y)%q for x,y in zip(a,b))
    def cmul(a,b):
        x,y,z,w,v=a;p,r,s,t,u=b
        return (x*p%q,(x*r+y*p)%q,(z*s-w*t)%q,(z*t+w*s)%q,v*u%q)
    def cpow(a,k):
        out=one
        for _ in range(k):out=cmul(out,a)
        return out
    f=[a for a in product(range(q),repeat=5) if cpow(a,q)==a]
    assert set(f)=={(a,0,b,0,c) for a,b,c in product(range(q),repeat=3)}
    es=[one]
    for b in [(1,0,1,0,0),(0,0,1,0,1),(1,0,0,0,0)]:
        es=[e for old in es for lam in range(q)
            if (e:=cmul(old,sub(one,cpow(sub(b,tuple(lam*x%q for x in one)),q-1))))!=zero]
    assert set(es)=={(1,0,0,0,0),(0,0,1,0,0),(0,0,0,0,1)}
    return {'ambient_elements':q**5,'frobenius_fixed_elements':len(f),'primitive_idempotents':len(es)}

def main():
    rng=random.Random(10426);q=3;gl=gl2(q);I=(1,0,0,1);cases=[]
    for k in range(13):
        s=(1,1) if not k else tuple(rng.randrange(1,q) for _ in range(2))
        t=(1,2) if not k else tuple(rng.randrange(1,q) for _ in range(2))
        sb=(I,)*3 if not k else tuple(rng.choice(gl) for _ in range(3))
        tb=(I,)*3 if not k else tuple(rng.choice(gl) for _ in range(3))
        actual,number=exhaustive_determinants(action(diagonal(s),sb,q),action(diagonal(t),tb,q),gl,q)
        expected,ref=expected_direct_sum(s,t,tb,sb,q)
        assert actual==expected
        if not k:assert (1,1,1) in actual and (1,1,1) not in ref
        cases.append({'case':k,'transporters':number,'determinant_triples':len(actual),
                      'SL_yes':(1,1,1) in actual,'reference_matching_SL_yes':(1,1,1) in ref})
    report={'status':'PASS','field':'F3','actual_tensor_pairs':len(cases),
            'A_B_combinations_tested':len(cases)*len(gl)**2,'cases':cases,
            'fixed_algebra_fixture':fixed_algebra_control(),
            'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'scope':'Exhaustive GL transporters on tiny tensors and exact Frobenius algebra fixture; finite controls, not the proof or an SL-TI implementation.'}
    (HERE/'CONTROLS.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in report.items() if k!='cases'}))

if __name__=='__main__':main()
