# Counting permutations by the intersection spaces of two codes

Let $C,D$ be binary codes of length $r$. Take a generator matrix of $C$ with columns $g_i$ and a parity-check matrix of $D$ with columns $h_j$. For a column list $M$ and a coordinate subset $S$, write
$$
B_M(S)=\operatorname{span} M_S\cap\operatorname{span} M_{S^c},\qquad
\lambda_M(S)=\dim B_M(S),\qquad
b_M(j)=\max_{|S|=j}\lambda_M(S).
$$
A tree below is rooted binary with the coordinates at its leaves. Each node is identified with the set of leaves below it. Put
$$
L(G,H)=\min_{\mathcal T}\max_{S\in\mathcal T}
               \lambda_G(S)\, b_H(|S|),\qquad
L_*=\min\{L(G,H),L(H,G)\}.
$$

**Theorem.** The exact number of coordinate permutations carrying $C$ into $D$, and one such permutation when the count is positive, can be computed deterministically in $2^{O(r+L_*)}$ bit operations. The input consists only of the two codes. In particular $2^{O(r)}$ suffices when either code has bounded branchwidth, with arbitrary dimension gap and arbitrary other code. More generally it suffices that the branchwidth of either column matrix multiplied by the smaller of the rank and corank of the other is $O(r)$. Here branchwidth uses the connectivity value $\lambda$ rather than $\lambda+1$.

**The interface.** A permutation $\pi$ is admissible exactly if its total matrix syndrome is zero,
$$
\sum_i g_i h_{\pi(i)}^{\mathsf T}=0.
$$
This is the generator and parity-check equation for inclusion. If a partial bijection sends $S$ onto $T$, write $X$ for the sum restricted to $S$. Its columns lie in $\operatorname{span}G_S$, and its rows lie in $\operatorname{span}H_T$. In a full solution the complementary partial sum equals $X$, by characteristic two. Thus completing this partial bijection requires
$$
X\in B_G(S)\otimes B_H(T).
$$
Indeed a matrix with columns in $U$ and rows in $V$ lies in $U\otimes V$, by putting bases of the two spaces first in independent changes of basis. This interface holds even for zero or repeated columns. The matrix syndrome formulation also appears in the literature on subcode equivalence. The connectivity spaces and their use in tree realizations of a *single* code are classical. [Santini, Baldi and Chiaraluce](https://eprint.iacr.org/2022/1749) · [Kashyap, On Minimal Tree Realizations of Linear Codes](https://arxiv.org/abs/0711.1383)

**Counting recurrence.** Fix a source tree and its ordered children. For each node $S$ and each target set $T$ of size $|S|$, keep a count indexed by the interface matrices $X$. For one source coordinate and one target coordinate the sole possible bijection has syndrome $g_i h_j^{\mathsf T}$. Keep it with count one if it belongs to the interface. For children $S_1,S_2$, split $T$ into $T_1,T_2$ of matching sizes, and for each child pair $(X_1,X_2)$ add the product of counts at $X=X_1+X_2$ when $X$ belongs to the parent interface. Record one contributing transition per nonzero count. Membership can be checked by two collections of linear equations on rows and columns. At the root the interface is zero.

Every retained partial assignment satisfies its own syndrome equation and the interface condition at each descendant. Disjoint union of the two child assignments gives exactly one parent assignment, whose restrictions to the fixed labelled child sets recover the contributing partition and child assignments uniquely. Consequently every counted root assignment is a valid bijection. Conversely every global solution passes every interface test by the complementary-sum identity. Induction proves exact counting. Following stored transitions yields the individual coordinate matches. The two empty codes of length zero admit the unique empty permutation.

**Cost and tree selection.** Compute all subset ranks by elimination. Then $\lambda_M(S)=\operatorname{rank} M_S+\operatorname{rank}M_{S^c}-\operatorname{rank}M$ gives both size profiles. For fixed orientation assign cost $c(S)=\lambda_G(S)b_H(|S|)$. The best tree value on a singleton is $c(S)$. On any larger set it is the maximum of $c(S)$ and
$$
\min_{\varnothing\ne U\subsetneq S}
       \max\{v(U),v(S\setminus U)\}.
$$
The recurrence follows by cutting the tree at the root. It computes the exact optimum and a tree in $3^r r^{O(1)}$ time. Try both orientations, since inverse permutations exchange $G,H$ by transposing all syndromes. For the better tree, each table has at most $2^{L_*}$ entries. The target splits at a fixed node number at most $3^r$ over all target sets. Child pairs therefore cost at most $3^r4^{L_*}r^{O(1)}$ bit operations over the whole fixed tree. Counts have at most $\log_2(r!)+1$ bits. The number of stored entries, including backpointers, is at most $2^{r+L_*}r^{O(1)}$. Finally $\lambda_M(S)\le\min(\operatorname{rank} M,r-\operatorname{rank} M)$, using the rank formula. A code and its dual have identical connectivity functions, since $\operatorname{rank}(M^*)_S=|S|-\operatorname{rank}M+\operatorname{rank} M_{S^c}$ for a matrix of the dual code. This proves both branchwidth claims.

For example, a direct sum of arbitrary codes on at most $b$ coordinates has branchwidth at most $b$, by first grouping each summand's leaves and then joining the summands. The theorem handles an unbounded number of summands, with another code that need not decompose in the same way. For the associated two-prime groups $G(C),G(D)$ the exact number of epimorphisms is the computed count multiplied by $6^r2^{r(r-\dim D)}$. Their Cayley tables have size exponential in $r$, and the codes are recoverable from promised tables. Thus $L_*=O(r)$ gives polynomial table-time counting and construction on this group family. [Group construction, code extraction and epimorphism formula, §5](https://github.com/Dugongue/MathProofs/blob/main/SylowTowerActionRanks/PROOF.md)

The same recurrence counts monomial containments over any explicitly represented finite field of size $q$. Include one nonzero scalar at each matched coordinate. The contribution at a leaf is the corresponding scalar times $g_i h_j^{\mathsf T}$, and at the root the total must vanish. The complementary sum is now $-X$, which lies in the same interface as $X$. For a zero outer product initialize its zero entry to $q-1$. For a nonzero outer product either no nonzero multiple belongs to the interface or all $q-1$ distinct multiples do. In the latter case the interface has dimension at least one. The resulting complexity is $3^r q^{2L_*}\operatorname{poly}(r,\log q)$ bit operations with standard polynomial-time field arithmetic. Unit scalars at every leaf recover ordinary permutation containment. Restricting leaf pairs to any supplied list of permitted assignments gives the corresponding constrained counts.

## Searching for a compatible tree on both sides

There is also an exact, witness-dependent test. For a threshold $L$, the question is whether some admissible $\pi$ and source tree satisfy $\lambda_G(S)\lambda_H(\pi S)\le L$ at every node. Decide this in $2^{O(r+L)}$ time with recovery of a permutation and a tree. Use all pairs $(S,T)$ of nonempty equally sized subsets, discard pairs whose connectivity product exceeds $L$, and retain reachable interface matrices as before. At a join try all aligned splits of **both** sets. The restrictions of a witnessing tree survive the cutoff and the complementary-sum test. Conversely a root backpointer constructs a tree and a bijection satisfying the promised inequalities. There are at most $9^r$ pairs of ordered splits across the complete recursion and at most $4^L$ child-state pairs per split. The fixed-tree counting recurrence above ensures each permutation is counted once. Allowing arbitrary trees here gives existence and witness recovery.

The two-sided search can succeed with both branchwidths unbounded and a linear dimension gap. Let $s\ge3$, $m=2^s-1$, and let $Q$ be the direct sum of the binary simplex code of length $m$ and $m$ two-coordinate repetition codes. Thus $Q$ has length $3m$, dimension $s+m$, full support and only even-weight words. Let $R$ be repetition on $3m$ coordinates. Choose $C=Q\oplus R$ and $D^\perp=R\oplus Q$, allowing independent coordinate scrambles afterward. The identity before scrambling is admissible by evenness. Both syndrome matrices have rank $s+m+1$ at length $r=6m$, and the dimension gap is $4m-2s-2$.

Every binary tree on the $m$ simplex leaves has an edge with both sides of size at least $m/3$. For instance, follow any child with more than $2m/3$ leaves until there is none, then its larger child has between $m/3$ and $2m/3$ leaves. Each side spans dimension at least $s-1$, since a subspace of dimension $s-2$ contains only $2^{s-2}-1$ nonzero columns. Thus some cut has simplex connectivity at least $s-2$. Restricting any full tree to its simplex leaves and suppressing unary nodes shows the same lower bound for each full matrix, since the remaining summands' connectivities are nonnegative. Nevertheless a common tree can first separate the two halves, then the summands of $Q$. Inside each half one matrix has connectivity at most one and the other at most $s$ for the chosen tree. Hence the matching passes the two-sided search with $L=s$, including after arbitrary independent scrambling.

The fixed-tree result solves every instance with $L_*=O(r)$. A rejection by the two-sided search at a smaller cutoff excludes only witnesses having a tree within that cutoff. The unrestricted linear-exponent bound and publication priority remain open here.

## Reproducible small control

This Python control compares the fixed-tree recurrence with direct permutation of every codeword. It uses every ordered pair of the 67 binary codes of length four, including zero coordinates, repeated columns and the full space. The mathematical proof covers arbitrary length.

```python
from functools import cache
from itertools import permutations


def span(vectors):
    values = {0}
    for v in vectors:
        values |= {u ^ v for u in values}
    return frozenset(values)


def basis(space):
    rows, generated = [], {0}
    for u in sorted(space):
        if u not in generated:
            rows.append(u)
            generated |= {v ^ u for v in generated}
    return rows


def codes(r):
    found = {frozenset({0})}
    todo = list(found)
    while todo:
        c = todo.pop()
        for u in range(1 << r):
            if u in c:
                continue
            larger = c | {v ^ u for v in c}
            if larger not in found:
                found.add(larger)
                todo.append(larger)
    return found


def subsets(mask):
    t = mask
    while t:
        yield t
        t = (t - 1) & mask


@cache
def boundary(rows, r):
    full = (1 << r) - 1
    col = tuple(sum(((v >> j) & 1) << i for i, v in enumerate(rows))
                for j in range(r))
    spaces = [span(col[i] for i in range(r) if (s >> i) & 1)
              for s in range(1 << r)]
    cuts = [spaces[s] & spaces[full ^ s] for s in range(1 << r)]
    return col, cuts


def count_tree(g, h, r):
    # Fixed balanced source tree. Every coordinate bijection has one derivation.
    gs, gc = boundary(g, r)
    hs, hc = boundary(h, r)
    full = (1 << r) - 1

    @cache
    def table(s, t):
        domain = [i for i in range(r) if (s >> i) & 1]

        def admissible(x):
            rows = [(x >> (r*i)) & full for i in range(r)]
            return all(row in hc[t] for row in rows) and all(
                sum(((row >> j) & 1) << i for i, row in enumerate(rows)) in gc[s]
                for j in range(r))

        if len(domain) == 1:
            i, j = domain[0], t.bit_length() - 1
            x = sum(hs[j] << (r*u) for u in range(r) if (gs[i] >> u) & 1)
            return {x: 1} if admissible(x) else {}
        s1 = sum(1 << i for i in domain[:len(domain)//2])
        result = {}
        for t1 in subsets(t):
            if t1.bit_count() != s1.bit_count():
                continue
            for x, a in table(s1, t1).items():
                for y, b in table(s ^ s1, t ^ t1).items():
                    if admissible(x ^ y):
                        result[x ^ y] = result.get(x ^ y, 0) + a*b
        return result

    return table(full, full).get(0, 0)


def control(r=4):
    permutations_on_words = [
        [sum(((v >> i) & 1) << p[i] for i in range(r)) for v in range(1 << r)]
        for p in permutations(range(r))]
    spaces = codes(r)
    for c in spaces:
        images = [{p[v] for v in c} for p in permutations_on_words]
        g = tuple(basis(c))
        for d in spaces:
            dual = {w for w in range(1 << r)
                    if all((w & u).bit_count() % 2 == 0 for u in d)}
            h = tuple(basis(dual))
            assert count_tree(g, h, r) == sum(image <= d for image in images)
    print(len(spaces)**2, "ordered pairs checked")


if __name__ == "__main__":
    control()
```
