"""Independent exact audit primitives; no use of root orbit collapse or SDP matrices."""
from fractions import Fraction
from collections import defaultdict
from itertools import product

ZERO=(Fraction(0),)*3
ONE=(Fraction(1),Fraction(0),Fraction(0))
C=(Fraction(0),Fraction(1),Fraction(0))

def field(x):
    if isinstance(x,(tuple,list)):
        assert len(x)==3
        return tuple(Fraction(v) for v in x)
    return (Fraction(x),Fraction(0),Fraction(0))

def add(x,y): return tuple(a+b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def sub(x,y): return add(x,neg(y))
def scale(x,y): return tuple(a*Fraction(y) for a in x)
def mul(x,y):
    out=[Fraction(0)]*5
    for i,a in enumerate(x):
        for j,b in enumerate(y):out[i+j]+=a*b
    # c^3 = 3c/4 + 1/8; descending reduction also handles c^4.
    for k in (4,3):
        out[k-3]+=out[k]/8
        out[k-2]+=3*out[k]/4
    return tuple(out[:3])

def setting(a): return 0 if a==0 else 1 if a in (1,2,3) else 2

def reduce_word(word):
    out=[]
    for a in word:
        if out and setting(out[-1])==setting(a):
            if a!=out[-1]:return None
        else:out.append(a)
    return tuple(out)

def padd(*polys):
    out={}
    for p in polys:
        for w,x in p.items():
            out[w]=add(out.get(w,ZERO),x)
    return {w:x for w,x in out.items() if x!=ZERO}

def pscale(p,s):
    s=field(s)
    return {w:mul(x,s) for w,x in p.items() if mul(x,s)!=ZERO}

def pmul(p,q):
    out={}
    for u,x in p.items():
        for v,y in q.items():
            w=reduce_word(u+v)
            if w is not None:out[w]=add(out.get(w,ZERO),mul(x,y))
    return {w:x for w,x in out.items() if x!=ZERO}

def pstar(p):return {tuple(reversed(w)):x for w,x in p.items()}

def subst(poly,images):
    out={}
    for w,x in poly.items():
        term={():x}
        for a in w:term=pmul(term,images[a])
        out=padd(out,term)
    return out

WORDS=[()]
for n in (1,2,3):
    WORDS += [w for w in product(range(7),repeat=n)
              if all(setting(w[j])!=setting(w[j+1]) for j in range(n-1))]
assert len(WORDS)==170

def parent_amplitudes():
    out=[]
    a=sub(mul(C,C),field(Fraction(1,4)))
    for x in range(3):
        y,z=[j for j in range(3) if j!=x]
        out.append({(x,):a,(x,y):C,(x,z):C,(x,y,z):ONE,(x,z,y):ONE})
    for x in range(3):
        for y in range(3):
            if y!=x:out.append({(x,y,x):ONE,(x,):field(Fraction(-1,4))})
    return out

def gram_polynomial(amplitudes,gram):
    assert len(amplitudes)==len(gram)==len(gram[0])
    out={}
    for i,p in enumerate(amplitudes):
        for j,q in enumerate(amplitudes):
            z=field(gram[i][j])
            if z==ZERO:continue
            for u,x in p.items():
                for v,y in q.items():
                    word=reduce_word(tuple(reversed(u))+v)
                    if word is not None:
                        out[word]=add(out.get(word,ZERO),mul(z,mul(x,y)))
    return out

def marginal_from_parent(Z):
    # Generic indices 0,1,2 denote three different settings, unlike the
    # quotient indices below. Keep generic products unreduced until substitution.
    generic={}
    amplitudes=parent_amplitudes()
    for i,p in enumerate(amplitudes):
        for j,q in enumerate(amplitudes):
            z=field(Z[i][j])
            if z==ZERO:continue
            for u,x in p.items():
                for v,y in q.items():
                    word=tuple(reversed(u))+v
                    generic[word]=add(generic.get(word,ZERO),mul(z,mul(x,y)))
    out={}
    for b,d in product(range(4),repeat=2):
        q={(b+1,):ONE} if b<3 else {():ONE,(1,):neg(ONE),(2,):neg(ONE),(3,):neg(ONE)}
        r={(d+4,):ONE} if d<3 else {():ONE,(4,):neg(ONE),(5,):neg(ONE),(6,):neg(ONE)}
        out=padd(out,subst(generic,[{(0,):ONE},q,r]))
    eta=scale(add(ONE,C),Fraction(1,3))
    return padd(out,{(0,):neg(eta)})

def marginal_from_word_gram(Y):
    return gram_polynomial([{w:ONE} for w in WORDS],Y)

if __name__=='__main__':
    assert mul(mul(C,C),C)==(Fraction(1,8),Fraction(3,4),Fraction(0))
    assert reduce_word((1,1,4,4,0,0))==(1,4,0)
    assert reduce_word((1,2)) is None
    print('Independent exact algebra primitives passed self-checks.')


