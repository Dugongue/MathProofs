"""Small independent ring-map checks for Frobenius source counting."""
from itertools import product


def algebra(bounds, total=None):
    basis = [a for a in product(*(range(b) for b in bounds)) if total is None or sum(a)<total]
    positions = {a:i for i,a in enumerate(basis)}
    prime=3
    def multiply(x,y):
        z=[0]*len(basis)
        for i,a in enumerate(basis):
            for j,b in enumerate(basis):
                monomial=tuple(u+v for u,v in zip(a,b))
                k=positions.get(monomial)
                if k is not None:
                    z[k]=(z[k]+x[i]*y[j])%prime
        return tuple(z)
    return basis,multiply


def rank(rows):
    echelon={}
    for values in rows:
        a=list(values)
        for j in range(len(a)):
            if not a[j]:
                continue
            if j in echelon:
                a=[(x-a[j]*y)%3 for x,y in zip(a,echelon[j])]
            else:
                inverse=pow(a[j],-1,3)
                echelon[j]=tuple(x*inverse%3 for x in a)
                break
    return len(echelon)


def main():
    checked=0
    for bounds,total,exponents in [
        ((2,),None,(1,)),
        ((3,3),2,(1,1)),
        ((4,),None,(1,)),
        ((4,),None,(2,)),
        ((4,),None,(1,2)),
        ((3,),None,(1,1)),
    ]:
        basis,multiply=algebra(bounds,total)
        dimension=len(basis)
        zero=(0,)*dimension
        radical=list(product(range(3),repeat=dimension-1))
        radical=[(0,)+x for x in radical]
        head_positions=[j for j,a in enumerate(basis) if sum(a)==1]
        candidates=[]
        ns=[]
        us=[]
        for e in exponents:
            pool=[]
            for x in radical:
                y=x
                for _ in range(e):
                    y=multiply(multiply(y,y),y)
                if y==zero:
                    pool.append(x)
            candidates.append(pool)
            ns.append(next(n for n in range(dimension+1) if 3**n==len(pool)))
            us.append(rank([tuple(x[j] for j in head_positions) for x in pool]))
        counts={0:1}
        for u in us:
            next_counts={}
            for r,count in counts.items():
                next_counts[r]=next_counts.get(r,0)+count*3**r
                next_counts[r+1]=next_counts.get(r+1,0)+count*(3**u-3**r)
            counts={r:c for r,c in next_counts.items() if c}
        predicted=counts.get(len(head_positions),0)*3**sum(n-u for n,u in zip(ns,us))
        actual=0
        unit=(1,)+(0,)*(dimension-1)
        for generators in product(*candidates):
            rows=[unit]
            for g in generators:
                if rank(rows+[g])>len(rows):
                    rows.append(g)
            j=0
            while j<len(rows):
                for g in generators:
                    z=multiply(rows[j],g)
                    if rank(rows+[z])>len(rows):
                        rows.append(z)
                j+=1
            actual+=len(rows)==dimension
            checked+=1
        assert actual==predicted,(bounds,total,exponents,actual,predicted)
        print(bounds,total,exponents,"maps",actual)
    print(checked,"generator tuples independently checked")


if __name__=="__main__":
    main()
