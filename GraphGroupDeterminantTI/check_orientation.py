"""Check the marked orientation identity on all permutations of up to six points."""
from itertools import combinations, permutations

def orientation_displacement(mark, target_order, pi):
    target_position = {v:i for i,v in enumerate(target_order)}
    target_pair_indices = {frozenset(pair):i+1 for i,pair in enumerate(combinations(target_order,2))}
    source_sum_image = 0
    for first, second in combinations(mark,2):
        rank = target_pair_indices[frozenset([pi[first],pi[second]])]
        direction = 1 << rank
        if target_position[pi[first]]>target_position[pi[second]]:
            direction ^= 1
        source_sum_image ^= direction
    target_sum = sum(1<<j for j in target_pair_indices.values())
    return source_sum_image ^ target_sum

count=0
for n in range(7):
    for pi in permutations(range(n)):
        for mark_size in range(n+1):
            for mark in combinations(range(n),mark_size):
                target_order=tuple(sorted(pi[i] for i in mark))
                inv=sum(pi[i]>pi[j] for i,j in combinations(mark,2))
                assert orientation_displacement(mark,target_order,pi)==inv%2
                count+=1
print("Marked orientation checks:",count)
