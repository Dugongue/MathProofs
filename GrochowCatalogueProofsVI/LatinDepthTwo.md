# Depth-two Boolean size of Latin-square validity

## GP-0534

For an $n$ by $n$ table with binary symbol codes, the minimum DNF term count is exactly the number $L_n$ of Latin squares on the displayed labels. This remains true when the input is promised to have every row a permutation. Consequently both DNF sizes are $\exp(\Theta(n^2\log n))$. For the CNF on the full domain the elementary upper bound is $O(n^4)$ clauses, and the same upper bound holds on the row promise. For $n$ a power of two, there is an $\Omega(n^3)$ lower bound already with the row promise.

### Exact term count

Fix any conjunction satisfied by two Latin tables. Its satisfying set is a product across rows, because it constrains individual input bits. Mix one differing row of the second square with all other rows of the first. The mixed table still has permuted rows and still satisfies the conjunction. However, a single row change from a Latin square changes a position in some column to a value already appearing in that column in a different row. Hence the mixed table is not Latin. Each term of a correct DNF covers at most one Latin input, even on the promise. One full table description per Latin square attains the bound.

For completeness $L_n\le(n!)^n$. Given any first $k$ compatible rows, the allowed positions for the next row form an $(n-k)$-regular bipartite graph. The permanent lower bound for doubly stochastic matrices gives at least $n!((n-k)/n)^n$ perfect matchings in that graph. Multiplying the bounds for $k=0,\ldots,n-1$ gives $L_n\ge(n!)^{2n}/n^{n^2}$. Stirling's estimates imply the asserted exponential order. [Proof of the doubly stochastic permanent bound](https://doi.org/10.1016/0001-8708(81)90044-X) · [Depth-two Cayley-table lower bounds](https://arxiv.org/html/2608.26257v2)

### Clause bounds

Each pair of cells sharing a row or column and each legal symbol yield one clause forbidding both cells to encode that symbol. Forbidden codes need one clause per cell and code. This gives the displayed upper bounds.

For the lower bound assume $n=2^b$ and use the row-permutation restriction whose $i$th row has entries $x_i\oplus j$, where $0\le j<n$ indexes its columns and $x_i$ is a free $b$-bit label. Each output bit is a literal of one input bit. Such a table is Latin exactly when $(x_1,\ldots,x_n)$ is a permutation, so the CNF restricts without growing its clause count to one for the all-different predicate.

Sample an invalid tuple by choosing a uniformly random pair of duplicate positions, then two distinct uniform labels as the duplicate and missing labels, and finally permuting the other labels uniformly into the remaining positions. A clause that never rejects a permutation has a falsification set described by one list $A_i$ per row label. Each list is either empty, the full alphabet, or a binary subcube of size at most $n/2$. Ignore an empty falsification set. By Hall's theorem the lists have a fixed set of positions $S$ of size $k$ with union $U$ of size less than $k$. A sampled tuple satisfying these lists requires $k\ge2$, $|U|=k-1$, and both duplicate positions in $S$. Conditional on this pair lying in $S$, the set of $k-1$ distinct labels seen there is uniform by symmetry. Thus the probability of falsifying the clause is at most
$$
\frac{\binom{k}{2}}{\binom n2\binom n{k-1}}.
$$
This is $O(n^{-3})$ for $2\le k\le n-2$. For $k=n-1$ or $n$, every list in $S$ is proper. Inspect $\lfloor n/4\rfloor$ fixed positions in $S$ after conditioning on the duplicate pair. Discard one inspected position if necessary so that the visible labels are distinct. These labels constitute a uniform ordered sample without replacement, again by symmetry. On each inspection, the probability of landing in its list is at most $(n/2)/(n-\lfloor n/4\rfloor+1)\le 2/3$, even conditional on the earlier labels. This gives an exponentially small bound also in these cases. Since every sampled tuple must be rejected by at least one clause, the union bound requires $\Omega(n^3)$ clauses. The exact CNF order between these displayed bounds remains open here.
