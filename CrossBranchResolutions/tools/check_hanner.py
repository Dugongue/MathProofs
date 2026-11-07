"""Floating-point diagnostics for the regularized Hessian identity, not a proof."""
import cmath, itertools, json, math
from pathlib import Path

def matrices(a, p, eps, grid):
    n=len(a); direct=[[0.0]*n for _ in range(n)]; gram=[[0.0]*n for _ in range(n)]
    phases=[cmath.exp(2j*math.pi*(j+.271)/grid) for j in range(grid)]
    count=grid**(n-1)
    for rest in itertools.product(phases,repeat=n-1):
        z=(1+0j,)+rest; s=sum(ai*zi for ai,zi in zip(a,z)); t=eps+abs(s)**2
        u=[(s.conjugate()*zi).real for zi in z]; v=[(s.conjugate()*zi).imag for zi in z]
        w=t**((p-4)/2)
        for i in range(n):
            for j in range(n):
                c=(z[i].conjugate()*z[j]).real
                direct[i][j]+=w*(t*c+(p-2)*u[i]*u[j])/p
                if i==j: direct[i][j]+=(1-p)/p/a[i]*t**((p-2)/2)*u[i]
                gram[i][j]+=(2-p)*w*(v[i]*v[j]+eps/p*c)
    return [[x/count for x in row] for row in direct], [[x/count for x in row] for row in gram]

cases=[]
for a in [(1.,1.),(.6,1.,1.4),(1.,1.,1.)]:
    for p in [.5,1.,1.5,3.]:
        direct,gram=matrices(a,p,.3,128)
        error=max(abs(x-y) for r,s in zip(direct,gram) for x,y in zip(r,s))
        assert error<1e-8,(a,p,error)
        cases.append(dict(a=a,p=p,epsilon=.3,grid=128,max_abs_error=error))
result=dict(status='PASS',purpose='Numerical diagnostic only; universal proof is analytic',cases=cases,max_abs_error=max(c['max_abs_error'] for c in cases))
Path(__file__).with_name('hanner-numerics.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'status':result['status'],'cases':len(cases),'max_abs_error':result['max_abs_error']}))
