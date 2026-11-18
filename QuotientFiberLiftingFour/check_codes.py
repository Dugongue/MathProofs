from itertools import combinations, permutations

def span(rows):
    result = {0}
    for v in rows:
        result |= {x ^ v for x in result}
    return frozenset(result)

def spaces(ambient):
    known = {frozenset({0})}
    front = list(known)
    while front:
        U = front.pop()
        for v in ambient - U:
            V = U | {u ^ v for u in U}
            if V not in known:
                known.add(V)
                front.append(V)
    return known

def perms(C,k):
    for sig in permutations(range(k)):
        yield frozenset(sum(((x >> i) & 1) << j for i,j in enumerate(sig)) for x in C)

total = 0
for k in range(1,5):
    all_codes=spaces(frozenset(range(1<<k)))
    below={d:[x for x in all_codes if x <= d] for d in all_codes}
    orbits={c:set(perms(c,k)) for c in all_codes}
    for c in all_codes:
        for d in all_codes:
            exact=any(x <= d for x in orbits[c])
            for w in (1,2,3):
                a=(len(span(x for x in c if x.bit_count()==w))).bit_length()-1
                hits=set()
                for words in combinations([x for x in d if x.bit_count()==w],a):
                    U=span(words)
                    if len(U)==1<<a:
                        hits.update(x for x in below[d] if U<=x and len(x)==len(c))
                assert bool(hits & orbits[c])==exact,(k,c,d,w)
                total+=1
print(total,"code-pair / weight tests agree with permutation enumeration.")
