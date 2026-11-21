# Small homomorphism separators and Boolean graph-invariant degree

## GP-0922. The unrestricted size of a separator is linear, even at rank width one

**Theorem.** Every pair of nonisomorphic simple $n$-vertex graphs is distinguished by the count of homomorphisms from an effectively constructible graph with at most $n$ vertices. For every $n\ge4$, there are pairs of graphs of rank width one for which the smallest distinguishing test has $\lfloor n/2\rfloor+1$ vertices. Thus the worst test size is $\Theta(n)$ for every positive rank-width allowance. Rank width zero permits only edgeless graphs and hence has no nonisomorphic pair of common order.

For the upper bound use the finite triangular argument from Lovász's homomorphism theorem. Fix one candidate target $G$ as a labelled source. Its induced injective count into itself is positive. The same count into the other $n$-vertex target $H$ is zero. Inclusion-exclusion on the nonedges of $G$ expands this count into a signed sum of injective homomorphism counts of supergraphs on those same vertices. For each injective count, further expand by inversion on the lattice of vertex partitions:
$$
\operatorname{inj}(F,Y)=
\sum_{\pi}\mu(\widehat 0,\pi)\operatorname{hom}(F/\pi,Y).
$$
An image kernel is exactly one partition. A quotient with loops contributes zero for simple targets, and repeated edges have the same effect as one edge. Therefore if all the counts of the resulting quotient tests agreed, the induced injective count would agree too. Construct a test by enumerating supergraphs of $G$ and their partitions, testing each resulting homomorphism count by finite enumeration. This procedure is effective, and its size guarantee concerns the test order, with no claim of a polynomial-time search. [Lovász, Operations with structures](https://doi.org/10.1007/BF02280291) · [Sparse-test context](https://arxiv.org/abs/2601.18602)

For the lower bound, let $P_a$ denote the path on $a$ vertices and fix $m\ge1$. Compare
$$
X=P_m\sqcup P_{m+2},\qquad Y=P_{m+1}\sqcup P_{m+1}.
$$
They are distinct and each has rank width one. Each path has a caterpillar rank decomposition with interval cuts crossing at most one edge, and one can join the two path decompositions through a cut with no crossing edges.

For a finite connected graph $F$, fix a vertex $u$. A homomorphism to the integer line is a map $f$ taking adjacent vertices to consecutive integers. There are finitely many such maps with $f(u)=0$. Define $w(f)=\max_v f(v)-\min_v f(v)$. After a translation of all images, this map has exactly $\max(0,a-w(f))$ placements in $P_a$. Hence
$$
\operatorname{hom}(F,P_a)=\sum_{f\colon \,f(u)=0}\max(0,a-w(f)).
$$
If $F$ has at most $m+1$ vertices, its diameter and therefore $w(f)$ are at most $m$. For $a=m,m+1,m+2$ each summand is then affine in $a$. It follows that $\operatorname{hom}(F,X)=\operatorname{hom}(F,Y)$ for every connected such $F$. Disconnected counts multiply across components.

The source $P_{m+2}$ distinguishes. Its two monotone rooted maps to the integer line have $w=m+1$, giving a contribution of $1$ each to $X$ and zero to $Y$. All other maps have $w\le m$ and cancel in the difference. For odd $n$, add one isolated vertex to both targets, which preserves the argument and rank width. For $n=2m+2$ or $2m+3$ the smallest test therefore has exactly $m+2=\lfloor n/2\rfloor+1$ vertices. This lower bound already uses targets of rank width one and applies even if every finite simple graph is allowed as a test.

## GP-0886. Linear lower and logarithmic-orbit upper bounds for subgraph orbit sums

**Theorem.** Let $d(n)$ be the least degree so that all squarefree graph-subpattern orbit sums of degree at most $d(n)$ separate simple Boolean adjacency orbits on $n$ vertices in characteristic zero. For every $n\ge4$,
$$
\left\lfloor n/2\right\rfloor
\ \le d(n) \le\
\min\!\left\{
\left\lfloor \tfrac12\binom n2\right\rfloor,
1+\lfloor\log_2(n!)\rfloor
\right\}.
$$
The upper and lower bounds apply to joint separation by the entire family, with no assumption that its members can all be evaluated efficiently. [Thiéry, algebraic graph invariants](https://arxiv.org/abs/0812.3082)

For the lower bound take the path pair above. The argument gives equal homomorphism counts of every connected graph with at most $m$ **edges**, since $w(f)\le m$ for a connected graph of at most that many edges. Multiplicativity extends this to disconnected patterns with at most $m$ edges as well. A quotient by a vertex partition cannot increase the edge count after removing duplicate edges, and looped quotients contribute zero. Partition inversion therefore gives equality of injective counts for all patterns of at most $m$ edges. A squarefree orbit sum for a graph pattern on the vertex set $[n]$, including any isolated vertices, is its injective count divided by its automorphism order. Thus all degree-at-most-$m$ orbit sums agree on these two distinct orbits. The lower bound follows with $m=\lfloor n/2\rfloor-1$.

For the logarithmic upper bound a simple moment-support lemma holds over any field. If a nonzero signed function $w$ on a Boolean cube annihilates every squarefree monomial of degree at most $d$, then $w$ has at least $2^{d+1}$ support points. For $d=0$ the condition $\sum_x w(x)=0$ forces at least two. For $d>0$ find a coordinate that takes both values on the support. Each nonzero slice annihilates all monomials of degree at most $d-1$ on the remaining coordinates. This is obtained by multiplying each monomial by the coordinate or by one minus it before evaluating the original moment. By induction each slice has at least $2^d$ support points.

Apply the lemma over $\mathbb Q$ to the difference between the uniform distributions on two distinct Boolean adjacency orbits. Its support size is at most $2n!$. If all degree-at-most-$d$ orbit sums agree, all individual monomial moments of degree at most $d$ agree as well. In fact, averaging a single monomial over the uniformly permuted adjacency matrices equals the corresponding orbit sum divided by the size of its monomial orbit. With $d=1+\lfloor\log_2(n!)\rfloor$, the moment-support lemma contradicts the support bound. In particular the upper bound is $O(n\log n)$.

For the other upper bound compare the edge counts first. If both targets have $e$ edges and $e\le\lfloor\binom n2/2\rfloor$, the orbit sum of the full edge monomial of one of them separates the pair. A target of the same size contains a copy of the whole edge pattern only if its orbit agrees. If $e>\binom n2/2$, apply the same observation to the complements. Substituting $1-x_{ij}$ for each edge variable writes the resulting invariant as a linear combination of squarefree orbit sums of degree at most $\binom n2-e$. This proves both upper bounds.
