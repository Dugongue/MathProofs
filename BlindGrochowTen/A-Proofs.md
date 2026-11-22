# Recovering a Frobenius cycle profile from partial observations

For a finite permitted set $S$ of positive cycle lengths, let $a_d$ denote the multiplicity of cycles of length $d$. Its mark at exponent $n$ is $F_a(n)=\sum_{d\in S,\ d\mid n} d a_d$, the number of fixed points under the $n$-th power. The same profiles model finite étale algebras over a finite field via the action of Frobenius on geometric points. On the trace-tensor family from the preceding work, recovering the profile therefore recovers the tensor orbit. [The Stacks Project, §58.2](https://stacks.math.columbia.edu/tag/04JI)

## Recovery from noisy fixed-point counts

For each $d\in S$, choose a sample exponent $n_d$ with $e\mid n_d$ if and only if $e\mid d$ for every $e\in S$. If two profiles satisfy
$$
|F_a(n_d)-F_b(n_d)|<d
$$
for every $d\in S$, the profiles agree. The first differing length $d$ would give $F_a(n_d)-F_b(n_d)=d(a_d-b_d)$, because every other measured divisor of $d$ has smaller length. In particular a noisy dataset with uncertainty intervals of diameter less than $d$ in row $d$ permits at most one profile. The proof allows arbitrary permitted lengths and sample exponents and uses the integer nature of the multiplicities.

## Recovery from noisy tensor-power tests

Let $G_d(X)=\sum_i c_{d,i}X^i$ with nonnegative integer coefficients. For each $d$, choose a positive exponent $j_d$ with $c_{d,j_d}>0$. If the observed values of $G_d(F_a(n_d))$ and $G_d(F_b(n_d))$ differ by less than $c_{d,j_d}d^{j_d}$ for all $d$, the profiles agree. If $v\ge u+d$ then $v^j-u^j\ge d^j$ for $j>0$, by expanding $(u+d)^j$. Every other coefficient contributes a nonnegative difference. The first differing length would thus force the displayed gap in its row.

Cartesian products multiply fixed-point marks, and disjoint unions add them. Thus $G_d$ can arise by measuring the $n_d$-th power of a direct sum of tensor powers of a finite étale object with fixed marker factors. The coefficients are the marks of the markers at $n_d$. For example, the cubic tensor power needs a difference of at least $d^3$ in the row of the first differing length. If that row starts at zero and the two underlying marks differ by exactly $d$, equality is achieved for the monomial $X^3$. This is an exact absolute-error certificate on the expanded counts.

## Recovery from two extensions via a graph

For two extension degrees $k,\ell$ form a bipartite multigraph. Each permitted degree $d\in S$ supplies one edge between $d/\gcd(d,k)$ in the left vertex class and $d/\gcd(d,\ell)$ in the right class. The extension decks report the sum of weights $d a_d$ incident to each vertex. Indeed a length-$d$ orbit splits into $\gcd(d,k)$ orbits of length $d/\gcd(d,k)$, so these weighted sums are exactly the total masses in the resulting cycle-length classes.

If the graph is a forest, the two extension decks recover the original profile on $S$. If profiles differ, the induced multigraph on their differing edges has an edge at a leaf vertex. In its fiber, every other edge has equal weight in the two profiles. Equality of the observed vertex sums gives equality of the weight on the selected edge. For example, the quadratic and cubic extensions recover profiles on $S=\{1,2,3\}$ in all dimensions.

Conversely, every cycle in the multigraph gives an exact pair of differing profiles with equal extension data. A pair of parallel edges counts as a cycle of length two. Write $L$ for the least common multiple of the edge lengths along the cycle. On alternate edges give the signed weights $+L$ and $-L$. At each vertex the signed sum vanishes, and each signed weight is divisible by its edge length. Dividing by edge length and using positive and negative parts gives nonnegative cycle multiplicities with the same dimension. Adding the length $6$ to $S=\{1,2,3\}$ creates the square for the quadratic/cubic example.

In the forest case a queue of leaves recovers the weights from exact decks in linear time in the number of edges and vertices, once the graph has been constructed. Remove a leaf and subtract its known incident weight from the opposite vertex. Repeat, then divide each extracted weight by its edge length. This is an application of the incidence-matrix model of sparse recovery to a pair of Frobenius powers. [Zhao, Kaba, Vidal, Robinson and Mallada](https://mallada.ece.jhu.edu/pubs/2018-CDC-ZKVRM.pdf)

## Scope of the formalization

The Lean theorems prove interval recovery, the amplified polynomial test, and the two-extension recovery in a finite-support model. The graph theorem assumes its equivalent leaf condition for every nonempty subset of edges. The graph equivalence, converse circulation, runtime and finite étale interpretation above have written proofs. The companion file also includes an alternate encoding of the exact marks into a single natural number using radix one larger than a known size bound. This stores the same observations as digits.

The blind structural selector froze 190 motifs out of 823 over a 590,787-declaration packed bank with seed 9380717. On reveal, positions 26 and 39 linked coprime divisibility and primitive-root-style divisibility. Positions 76, 106 and 117 contributed the divisor-support viewpoint. Positions 52 and 61 included a permutation cycle-type port, and position 92 contained squarefree division and gcd. These were starting points for the representation and support constraints. The recovery proofs assemble those ideas after reveal. [Frozen motifs](A-Frozen.json) · [Lean sources](A.lean)
