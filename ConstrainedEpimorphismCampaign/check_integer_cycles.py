"""Independent finite checks of integer threshold encoding and ideal penalties."""
from itertools import product, combinations


def energy(labels, edges):
    return sum(abs(labels[u]-labels[v]-z) for u,v,z in edges)


def threshold_energy(labels, edges, bound):
    result=0
    for u,v,z in edges:
        for t in range(min(-bound,-bound+z)+1,max(bound,bound+z)+1):
            result += ((labels[u]>=t) != (labels[v]>=t-z))
    return result


def main():
    tested=0
    for n in range(2,5):
        pairs=list(combinations(range(n),2))
        for offsets in product(range(-1,2),repeat=len(pairs)):
            edges=[(*pair,z) for pair,z in zip(pairs,offsets)]
            for rest in product(range(-2,3),repeat=n-1):
                x=(0,*rest)
                assert energy(x,edges)==threshold_energy(x,edges,2)
                tested+=1
    penalties=0
    for mask in range(8):
        relations=[pair for j,pair in enumerate([(0,1),(0,2),(1,2)]) if mask>>j&1]
        coeff=[0]*3
        for u,v in relations:
            coeff[v]+=1
            coeff[u]-=1
        def actual(x):
            total=sum(abs(x[v]-x[u]) for u,v in relations)
            total+=sum(c*abs(a) if c>=0 else -c*abs(a-1) for a,c in zip(x,coeff))
            return total+sum(abs(a)+abs(a-1) for a in x)
        optimum=actual((0,0,0))
        for x in product(range(-2,4),repeat=3):
            clipped=tuple(min(1,max(0,a)) for a in x)
            assert actual(clipped)<=actual(x)
            if x != clipped:
                assert actual(clipped)<actual(x)
            assert (actual(x)==optimum)==(all(a in (0,1) for a in x) and all(x[v]<=x[u] for u,v in relations))
            penalties+=1
    medians=0
    for n in range(1,8):
        for x in product(range(-1,2),repeat=n):
            ordered=sorted(x)
            med=ordered[n//2]
            distance=sum(abs(a-med) for a in ordered)
            matched=sum(ordered[-1-j]-ordered[j] for j in range(n//2))
            assert matched==distance
            medians+=1
    print(tested,"threshold identities,",penalties,"ideal penalty cases,",medians,"median pairings passed")


if __name__ == "__main__":
    main()
