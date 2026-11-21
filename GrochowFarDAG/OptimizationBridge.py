from itertools import combinations, permutations, product


def subsets(items):
    return (frozenset(part) for size in range(len(items) + 1)
            for part in combinations(items, size))


def allocated(labels, eligibility):
    """Return whether the chosen labels can occupy distinct slots."""
    return any(len(set(slots)) == len(labels)
               for slots in product(*(eligibility[e] for e in sorted(labels))))


def permanent_support(left, right):
    """Enumerate the nonzero terms of the explicit assignment matrix."""
    ell, r = 2, 2
    size = ell + len(left) + r
    arcs = {(v, v): None for v in range(size)}
    for e, (ls, rs) in enumerate(zip(left, right)):
        for v in ls:
            arcs[v, ell + e] = e
        for v in rs:
            arcs[ell + e, ell + len(left) + v] = None
    for target in range(ell):
        for source in range(ell + len(left), size):
            arcs[source, target] = None

    support = set()
    for permutation in permutations(range(size)):
        if all((v, to) in arcs for v, to in enumerate(permutation)):
            monomial = [arcs[v, to] for v, to in enumerate(permutation)
                        if arcs[v, to] is not None]
            assert len(monomial) == len(set(monomial))
            support.add(frozenset(monomial))
    return support


def graph_forest(edges):
    parents = {}

    def representative(v):
        while parents.get(v, v) != v:
            v = parents[v]
        return v

    for u, v in edges:
        u, v = representative(u), representative(v)
        if u == v:
            return False
        parents[u] = v
    return True


def independent(labels, hyperedges):
    """Literal enumeration of possible forest shrinkings."""
    pairs = [tuple(combinations(hyperedges[e], 2)) for e in sorted(labels)]
    return any(graph_forest(edges) for edges in product(*pairs))


def slots(hyperedges, reverse=None):
    """Unrestricted or order-filtered allocations for one given hypergraph."""
    choices = []
    for edge in hyperedges:
        eligible = ()
        if len(edge) >= 2:
            if reverse is None:
                eligible = edge
            else:
                min_in_order = (max if reverse else min)(edge)
                eligible = tuple(v for v in edge if v != min_in_order)
        choices.append(eligible)
    return choices


def graph_trials():
    edges = tuple(combinations(range(4), 2))
    labels = tuple(range(4))
    sets = tuple(subsets(labels))
    tests = 0
    for first in combinations(edges, 4):
        for second in permutations(first):
            left, right = slots(first), slots(second)
            exact = tuple(s for s in sets if independent(s, first)
                          and independent(s, second))
            relaxed = tuple(s for s in sets if allocated(s, left)
                            and allocated(s, right))
            assert set(exact) <= set(relaxed)
            for weights in product(range(3), repeat=4):
                optimum = max(sum(weights[e] for e in s) for s in exact)
                upper = max(sum(weights[e] for e in s) for s in relaxed)
                assert 2 * upper <= 3 * optimum <= 3 * upper
                tests += 1
    return tests


def hypergraph_trials():
    first = ((0, 1, 2), (0, 1, 2), (1, 2, 3), (0, 2, 3))
    sets = tuple(subsets(tuple(range(len(first)))))
    tests = 0
    for second in set(permutations(first)):
        exact = tuple(s for s in sets if independent(s, first)
                      and independent(s, second))
        relaxed = tuple(s for s in sets if allocated(s, slots(first))
                        and allocated(s, slots(second)))
        ordered = tuple(s for s in sets if any(
            allocated(s, slots(first, rev_first))
            and allocated(s, slots(second, rev_second))
            for rev_first, rev_second in product((False, True), repeat=2)))
        assert set(ordered) <= set(exact) <= set(relaxed)
        for weights in product(range(3), repeat=len(first)):
            optimum = max(sum(weights[e] for e in s) for s in exact)
            upper = max(sum(weights[e] for e in s) for s in relaxed)
            lower = max(sum(weights[e] for e in s) for s in ordered)
            assert upper <= 2 * optimum <= 2 * upper
            assert optimum <= 4 * lower <= 4 * optimum
            tests += 1
    return tests


def shared_cycle_test():
    first = ((0, 1), (1, 2), (0, 2), (3, 4), (4, 5))
    second = ((0, 1), (3, 4), (4, 5), (1, 2), (0, 2))
    weights = (3, 2, 2, 2, 2)
    labels = frozenset(range(5))
    assert allocated(labels, slots(first)) and allocated(labels, slots(second))
    valid_deletions = tuple(
        d for d in subsets(tuple(labels))
        if independent(labels - d, first) and independent(labels - d, second)
    )
    best = min(valid_deletions, key=lambda d: sum(weights[e] for e in d))
    assert best == frozenset({0})
    assert sum(weights[e] for e in best) == 3


def spanning_tree_trials():
    edges = tuple(combinations(range(4), 2))
    trees = tuple(part for part in combinations(range(len(edges)), 3)
                  if graph_forest(edges[e] for e in part))
    tests = 0
    for weights in product(range(3), repeat=len(edges)):
        optimal = max(sum(weights[e] for e in t) for t in trees)

        def ordered(reverse):
            return sum(max((0, *(
                weights[e] for e, edge in enumerate(edges)
                if vertex == (min if reverse else max)(edge)
            ))) for vertex in range(4))

        lower = max(ordered(False), ordered(True))
        assert lower <= optimal <= 2 * lower
        tests += 1
    return tests


def main():
    choices = tuple(tuple(s) for s in subsets((0, 1)))
    label_sets = tuple(subsets((0, 1)))
    matrix_tests = 0
    for a, b, c, d in product(choices, repeat=4):
        left, right = (a, b), (c, d)
        expected = {s for s in label_sets if allocated(s, left)
                    and allocated(s, right)}
        assert permanent_support(left, right) == expected
        matrix_tests += 1
    assert matrix_tests == 256
    assert graph_trials() == 29160
    assert hypergraph_trials() == 972
    assert spanning_tree_trials() == 729
    shared_cycle_test()
    print("256 permanent supports, 29,160 graph weight cases, "
          "972 hypergraph weight cases, 729 spanning-tree cases, "
          "and the shared-cycle deletion control passed.")


if __name__ == "__main__":
    main()

