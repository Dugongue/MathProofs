"""Independent exhaustive small-space checks of the proposed code-LU flag lemma."""
from itertools import combinations, product
from pathlib import Path
import hashlib
import json
import time

ROOT = Path(__file__).resolve().parent


def subspaces(N):
    for rank in range(N+1):
        for pivots in combinations(range(N),rank):
            free = [(i,j) for i in range(rank) for j in range(pivots[i]+1,N) if j not in pivots]
            for values in product(range(2),repeat=len(free)):
                rows = [1<<j for j in pivots]
                for (i,j),bit in zip(free,values):
                    rows[i] |= bit<<j
                words = {0}
                for row in rows:
                    words |= {x^row for x in words}
                yield rows,words


def physical_mask(A,n):
    return sum(3<<(2*i) for i in range(n) if A>>i&1)


def graph_parts(rows,n):
    parent = list(range(n))
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for row in rows:
        support = [i for i in range(n) if row>>(2*i)&3]
        for i in support[1:]:
            parent[find(i)] = find(support[0])
    return {frozenset(j for j in range(n) if find(j)==find(i)) for i in range(n)}


def main():
    start=time.monotonic()
    n=3
    count=flag_checks=preserving=0
    for rows,S in subspaces(2*n):
        count+=1
        projectors=[A for A in range(1<<n) if all(s&physical_mask(A,n) in S for s in S)]
        signatures=[tuple(A>>i&1 for A in projectors) for i in range(n)]
        independent_parts={frozenset(j for j in range(n) if signatures[j]==signatures[i]) for i in range(n)}
        assert graph_parts(rows,n)==independent_parts
        for T in range(1,1<<n):
            xmask=sum(1<<(2*i) for i in range(n) if T>>i&1)
            zmask=xmask<<1
            D={s for s in S if not s&xmask}
            K={s&~zmask for s in S}
            W=((1<<n)-1)^T
            for A in range(1<<n):
                if A&~W:
                    continue
                flag_checks+=1
                mask=physical_mask(A,n)
                if all(d&mask in D for d in D) and all(k&mask in K for k in K):
                    preserving+=1
                    assert all(s&mask in S for s in S), (rows,T,A)
                    if len(independent_parts)==1:
                        assert A==0
    assert count==2825
    receipt={'kind':'INDEPENDENT_EXHAUSTIVE_FINITE_CONTROL_NOT_UNIVERSAL_PROOF',
             'status':'PASS','all_subspaces_F2_6':count,
             'flag_projection_checks':flag_checks,'successful_flag_preservers':preserving,
             'physical_RREF_partitions_checked':count,'seconds':round(time.monotonic()-start,3),
             'source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'CODE-FLAGS-CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps(receipt))


if __name__=='__main__':
    main()
