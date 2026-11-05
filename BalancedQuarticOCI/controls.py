"""Independent exact finite controls. These are not a closure proof."""
from fractions import Fraction as F
from pathlib import Path
from itertools import combinations
import json

def eye(n): return {(i,i):F(1) for i in range(n)}
def linear(*terms):
    z={}
    for a,x in terms:
        for k,v in x.items(): z[k]=z.get(k,0)+a*v
    return {k:v for k,v in z.items() if v}
def mul(a,b):
    rows={}
    for (j,k),v in b.items(): rows.setdefault(j,[]).append((k,v))
    z={}
    for (i,j),u in a.items():
        for k,v in rows.get(j,[]): z[i,k]=z.get((i,k),0)+u*v
    return {k:v for k,v in z.items() if v}
def tensor(a,b,m):
    return {(i*m+k,j*m+l):u*v for (i,j),u in a.items()
            for (k,l),v in b.items()}
def inv(a,n):
    r=[[F(a.get((i,j),0)) for j in range(n)]+[F(i==j) for j in range(n)]
       for i in range(n)]
    for j in range(n):
        k=next((k for k in range(j,n) if r[k][j]),None)
        if k is None: raise ValueError("singular")
        r[j],r[k]=r[k],r[j]
        p=r[j][j]
        r[j]=[x/p for x in r[j]]
        for i in range(n):
            if i!=j and (u:=r[i][j]):
                r[i]=[x-u*y for x,y in zip(r[i],r[j])]
    return {(i,j):r[i][j+n] for i in range(n) for j in range(n) if r[i][j+n]}
def conjugate(x,g,n):
    return mul(mul(g,x),inv(g,n))
def tags(z,n):
    p,q={},{}
    for (i,j),v in z.items():
        a,b=divmod(i,n);c,d=divmod(j,n)
        if b==d: p[a,c]=p.get((a,c),0)+v
        if a==c: q[b,d]=q.get((b,d),0)+v
    return linear((1,p)),linear((1,q))
def standard(n):
    p={(i,i):F(1 if i<n else -1) for i in range(2*n)}
    q={(i,(i+n)%(2*n)):F(1) for i in range(2*n)}
    return p,q
def background(p,q,N):
    return linear((F(1,N),tensor(p,eye(N),N)),(F(1,N),tensor(eye(N),q,N)))
def data_block(r,n,in_color,out_color):
    N=2*n
    def pos(i,colors):
        a,b=divmod(i,n)
        return (colors[0]*n+a)*N+(colors[1]*n+b)
    return {(pos(i,out_color),pos(j,in_color)):v for (i,j),v in r.items()}
def embed(a,b,n):
    return linear((1,background(*standard(n),2*n)),
                  (1,data_block(a,n,(1,1),(0,0))),
                  (1,data_block(b,n,(0,0),(1,1))))
def validate(z,N):
    p,q=tags(z,N);I=eye(N)
    if mul(p,p)!=I or mul(q,q)!=I or linear((1,mul(p,q)),(1,mul(q,p))):
        return False
    e=linear((F(1,2),I),(F(1,2),p))
    f=linear((F(1,2),I),(F(-1,2),p))
    e2=tensor(e,e,N);f2=tensor(f,f,N)
    d=linear((1,z),(-1,background(p,q,N)))
    return d==linear((1,mul(mul(e2,d),f2)),(1,mul(mul(f2,d),e2)))
def section(p,q,n):
    N=2*n;e=linear((F(1,2),eye(N)),(F(1,2),p));qe=mul(q,e)
    for cols in combinations(range(N),n):
        s={(i,j+c*n):a for c,M in enumerate((e,qe)) for j,k in enumerate(cols)
           for i in range(N) if (a:=M.get((i,k),0))}
        try:
            si=inv(s,N)
            return s,si
        except ValueError: pass
    raise AssertionError("no frame")
def sample(n,shift):
    return {(i,j):F(((11*i+7*j+shift)%13)-6,1+(i+j)%3)
            for i in range(n) for j in range(n)
            if ((11*i+7*j+shift)%13)!=6}

def run():
    frames=[]
    for n in [1,2,3]:
        N=2*n;p,q=standard(n)
        for shift in [2,9]:
            a,b=sample(n*n,shift),sample(n*n,shift+1)
            z=embed(a,b,n)
            assert tags(z,N)==(p,q) and validate(z,N)
            g=eye(N)
            for i,j,u in [(0,N-1,F(2,3)),(N-1,0,F(-3,5)),
                          (n-1,n,F(1,7)),(n,0,F(5,8))]:
                if i!=j: g=mul(linear((1,eye(N)),(u,{(i,j):F(1)})),g)
            znew=conjugate(z,tensor(g,g,N),N*N)
            p1,q1=tags(znew,N)
            assert p1==conjugate(p,g,N) and q1==conjugate(q,g,N)
            assert validate(znew,N)
            s,si=section(p1,q1,n)
            assert conjugate(p,s,N)==p1 and conjugate(q,s,N)==q1
            sg=mul(si,g)
            h={(i,j):v for (i,j),v in sg.items() if i<n and j<n}
            assert sg==tensor(eye(2),h,n)
            hh=tensor(h,h,n)
            expected=embed(conjugate(a,hh,n*n),conjugate(b,hh,n*n),n)
            assert conjugate(znew,tensor(si,si,N),N*N)==expected
            sext=tensor(z,eye(N),N)
            recovered={}
            for (i,j),v in sext.items():
                a0,b0=divmod(i,N);a1,b1=divmod(j,N)
                if b0==b1: recovered[a0,a1]=recovered.get((a0,a1),0)+v/N
            assert recovered==z
            e=linear((F(1,2),eye(N)),(F(1,2),p))
            proj=tensor(e,e,N)
            flip=tensor(q,q,N)
            A1=mul(mul(mul(proj,z),flip),proj)
            A2=mul(mul(mul(proj,flip),z),proj)
            assert A1==data_block(a,n,(0,0),(0,0))
            assert A2==data_block(b,n,(0,0),(0,0))
            tr=lambda M: sum(v for (i,j),v in M.items() if i==j)
            assert tr(mul(A1,A2))==tr(mul(a,b))
            frames.append({"n":n,"sample":shift,"exact_checks":"PASS","invariant_lift":"PASS"})
    n=1;N=2;p,q=standard(n);base=background(p,q,N)
    wrong=linear((1,base),(1,data_block({(0,0):F(1)},n,(1,0),(0,1))))
    assert tags(wrong,N)==(p,q) and not validate(wrong,N)
    assert not validate({},N)
    a={(0,3):F(1)}
    degenerations=[]
    for t in [F(1),F(1,2),F(-2),F(0)]:
        at=linear((t*t,a))
        if t:
            h={(0,0):t,(1,1):F(1)}
            assert conjugate(a,tensor(h,h,2),4)==at
        zt=embed(at,{},2)
        assert tags(zt,4)==standard(2) and validate(zt,4)
        degenerations.append({"t":str(t),"nonzero_data":bool(at)})
    return {"status":"PASS","arithmetic":"exact rational",
            "nonorthogonal_tag_and_chart_fixtures":frames,
            "false_positive_controls":{"right_tags_wrong_channel":"rejected","zero":"rejected"},
            "genuine_degenerate_orbit_example":degenerations,
            "scope":"finite encoding and chart checks only; not proof of general closure statement"}
if __name__=="__main__":
    report=run()
    Path(__file__).with_name("CONTROLS.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
    print(json.dumps(report))
