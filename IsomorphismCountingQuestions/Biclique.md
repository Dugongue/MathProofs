# Exact counting complexity of homomorphism indistinguishability over bicliques

**Theorem.** Given two finite simple graphs, deciding whether they have equal numbers of homomorphisms from $K_{s,t}$ for every $s,t\ge 0$ is $\mathsf C_{=}\mathsf P$-complete under deterministic polynomial-time many-one reductions. Hardness holds when both input graphs are bipartite and uncolored.

Curticapean, Neuen, Nikabadi, Seppelt and Young explicitly pose this classification immediately before Theorem 7.1 of their dense Weisfeiler–Leman paper. The proof below is informal. A further consequence is many-one completeness of homomorphism indistinguishability over cliques on co-bipartite targets. Böker, Chen, Grohe and Rattan established completeness for the unrestricted clique problem under polynomial-time Turing reductions in Theorem 18 of their 2019 paper. [Biclique question](https://arxiv.org/html/2608.13382v1#S7) · [Clique theorem](https://doi.org/10.4230/LIPIcs.MFCS.2019.54)

## Membership

Let $N$ be the larger input graph order. For $a,b\ge 1$, the number of injective edge-preserving maps from labeled $K_{a,b}$ is a $\#\mathsf P$ function whenever $a+b\le N$. Guess the ordered images and check that they are distinct and every required edge is present. For larger $a+b$ the count is zero. A homomorphism from a biclique with positive sides can identify vertices only within its sides. Grouping homomorphisms by the partitions into fibers expresses every homomorphism count in terms of these injective counts. Conversely, isolating the partition into singletons and inducting on $a+b$ recovers the injective counts from homomorphism counts. Sources with an empty side give edgeless graph counts, determined by the order of the target. Form the sum of the squares of the two targets' count differences, including their order difference. There are polynomially many terms. This is a GapP function because GapP is closed under subtraction, products and polynomial sums. Its zero set is precisely the decision problem, proving membership.

## 1. A graph calculus for integer-weighted sums

Use bipartite *conflict* graphs $J$ with distinguished sides $L,R$ during the reduction. Write
$$
I_J(x,y)=\sum_{\substack{A\subseteq L,\ B\subseteq R\\
                          E_J(A,B)=\varnothing}}x^{|A|}y^{|B|}
$$
for the bivariate independence polynomial. The all-left and all-right pairs are included. Write $u=1+x,\ v=1+y$. Disjoint union of conflict graphs multiplies the full polynomials. Adding $p$ isolated left and $q$ isolated right vertices therefore multiplies by $u^p v^q$.

A pair $(J^+,J^-)$ is balanced when its two members have the same left size and the same right size. It represents the difference $I_{J^+}-I_{J^-}$. Such a difference is zero on both axes. To add the differences of balanced pairs, combine their positive members, and separately their negative members, by taking their disjoint union and **inserting all cross-part edges between different summands**. An independent choice that meets both sides must then be confined to one summand. Consequently the interior coefficients add. The two axes cancel because the result is balanced. Reversing a pair negates its difference.

For multiplication of balanced differences $P_+-P_-$ and $Q_+-Q_-$, use conflict-graph disjoint unions for the four products and the preceding addition rule to put $P_+Q_+$ and $P_-Q_-$ on one side, and $P_+Q_-$ and $P_-Q_+$ on the other. All four product graphs have identical left and right sizes, so their pure-axis terms cancel exactly. To multiply a balanced difference by a single graph polynomial, take the disjoint union with that graph on each side of the pair. These operations produce explicit bipartite graphs.

For $t\ge 2$, put alternating left and right vertices around an ordinary cycle. Its bivariate independence polynomial on $2t$ vertices is the trace of $(M(x)M(y))^t$, where
$$
M(z)=\begin{pmatrix}1&z\\1&0\end{pmatrix}.
$$
Indeed, successive column indices record the indicators of the selected vertices, adjacent selected indicators give a zero entry, and taking the trace closes the cycle. Since $\det(M(x)M(y))=xy$, the two-by-two identity $\operatorname{tr}(B^2)-\operatorname{tr}(B)^2=-2\det(B)$ gives
$$
I_{C_{4t}}-I_{C_{2t}\sqcup C_{2t}}=-2(xy)^t .
$$
These two conflict graphs are balanced. Swapping them gives a positive sign.

For a finite list of integer coefficients of bit length at most $b$, fix $D=2(b+1)$. For bit position $j=0,\ldots,b-1$, take $r=j+1$ factors of this cycle contrast, with exponents $t_1,\ldots,t_r\ge 2$ summing to $D$. Their product represents $2^{j+1}(xy)^D$. Build the product using a balanced binary tree. At a multiplication each child pair occurs at most twice across the resulting pair, so the total number of vertices is $O(rD)$, since the total number of vertices in the leaf pairs is $8D$ and each leaf is replicated by at most $2^{\lceil\log_2 r\rceil}$, and the explicit edge list is polynomial in that size. Thus for any coefficient $c$ on the list we can represent $2c(xy)^D$ in polynomial time by adding the pairs for its set bits and choosing signs. This common factor is what permits exponentially large integer coefficients with only polynomially many vertices.

It follows that for any polynomially long list of explicitly constructed bipartite graphs $J_d$ and polynomial-bit integers $c_d$, and nonnegative polynomially bounded exponents $p_d,q_d$, one balanced pair of polynomial size represents
$$
2(xy)^D\sum_d c_d u^{p_d}v^{q_d}I_{J_d}(x,y).
$$
Add zero pairs if needed when the sum is empty. All addition and multiplication here is performed by the graph constructions above.

## 2. Extract a count by one pair of graphs

Take a simple graph $H$ with $n_H$ vertices and $m_H$ edges. Its incidence conflict graph $J$ has one left vertex per vertex of $H$ and one right vertex per edge, with the usual incidence edges. Then
$$
I_J(x,y)=\sum_{S\subseteq V(H)}x^{|S|}v^{\,|E(H[V(H)\setminus S])|}.
$$
Setting $y=-1$ selects exactly the vertex covers $S$. Thus $[x^{n_H-k}]I_J(x,-1)$ counts independent $k$-sets in $H$, for $0\le k\le n_H$.

Choose upper bounds $n\ge n_H$ and $m\ge m_H$ shared by the two inputs whose counts will be compared. Write $P(u,v)=I_J(u-1,v-1)=\sum_{h,\ell}c_{h\ell}u^h v^\ell$, with degrees at most $n,m$. The desired scalar is
$$
s_H=\sum_{h=0}^n \binom{h}{n_H-k}c_{h0},
$$
using the zero convention for binomial coefficients. The coefficients $c_{h\ell}$ will never be computed by the reduction. Instead, for $0\le a\le n,\ 0\le b\le m$, replace each left vertex of $J$ by $a$ independent twins and each right vertex by $b$ independent twins, with complete cross edges between adjacent twin classes. Zero twins means deletion on that side. The resulting graph $J_{ab}$ satisfies
$$
I_{J_{ab}}(x,y)=P(u^a,v^b).
$$
A nonempty choice of left twins contributes $(1+x)^a-1$, and likewise on the right.

Define $V=(u^{ah})_{0\le a,h\le n}$ and $W=(v^{b\ell})_{0\le b,\ell\le m}$. Let $\Delta_n(u)=\det V$ and $\Delta_m(v)=\det W$. These polynomials are nonzero by the Vandermonde identity. With $C=(c_{h\ell})$, the matrix of explicit graph polynomials $B=(I_{J_{ab}})$ is $VCW^\mathsf T$. Multiplication by the two adjugates yields the polynomial identity
$$
\sum_{a,b}
\left(\sum_h\binom{h}{n_H-k}\operatorname{adj}(V)_{ha}\right)
\operatorname{adj}(W)_{0b}\,I_{J_{ab}}(x,y)
=\Delta_n(u)\Delta_m(v)\,s_H .
$$

All multipliers on the left can be computed explicitly in deterministic polynomial time. For example, a determinant of an $n$-row minor of $V$ has degree at most $n^3$ and coefficients of absolute value at most $n!$ by expansion over permutations. Compute it by evaluations at consecutive integer points through that degree, exact integer determinants and interpolation. The evaluations, denominators and intermediate arithmetic have polynomial bit length, since each evaluation point and degree is polynomially bounded. The same bounds apply to $W$ and to their univariate products as bivariate polynomials. Expanding the left side gives only polynomially many terms of the form admitted by the graph calculus in Section 1. The reduction knows all integer coefficients without knowing any independent-set count. For two inputs take the difference of the two expansions, using the same $n,m$ and the same $D$. The resulting balanced pair $(J^+,J^-)$ satisfies
$$
I_{J^+}-I_{J^-}=
2(xy)^D\Delta_n(1+x)\Delta_m(1+y)\,(s_H-s_{H'}).
\tag{1}
$$

## 3. Reduction and removal of the side labels

Equality of two $\#\mathrm{SAT}$ counts is $\mathsf C_{=}\mathsf P$-complete under many-one reductions. To recall why, express a GapP function as the difference of two accepting-path counts. The Boolean verifier of each count has one satisfying input per accepting path using canonical zero padding past termination. A Boolean circuit can be written as a 3-CNF with a variable for each gate and a unique extension of every satisfying input assignment. This produces two formulas whose count equality tests vanishing of the gap.

For each such 3-CNF build a graph having one group of vertices for each clause, consisting of the distinct satisfying assignments to its variables. Join vertices within each group, and join vertices in different groups exactly if their assignments conflict. An independent set of size $k$, the number of clauses, chooses one assignment per clause. The choices assemble uniquely into a satisfying assignment. Include a tautological unary-variable clause $(z\lor\neg z)$ for each unused variable so all variables occur. If a clause has no satisfying assignments, its contribution to the final comparison can be replaced by the identically zero expansion. The case $k>n_H$ also gives the identically zero expansion. The construction is polynomial in formula size and is parsimonious. Apply (1) to the two graphs.

Finally replace each conflict graph $J^\pm$ by its *bipartite complement* $G^\pm$, inserting exactly the missing edges between its sides, and forget both side labels. For $a,b\ge 1$, the number of injective maps from labeled $K_{a,b}$ into such a target equals $a!b!$ times the coefficient of $x^ay^b$ in
$$
I_{J^\pm}(x,y)+I_{J^\pm}(y,x).
$$
Every such injection lands in one connected component and respects its bipartition in one of the two orientations. This reasoning also counts both orientations when $a=b$. Equal sides across the balanced pair give equal target orders, so all edgeless sources agree. If the input counts are equal, identity (1) makes all biclique counts equal. If the counts differ, the symmetrized difference is nonzero: substitute $x=y=1$, where both Vandermonde determinants at $2$ are nonzero. Its axes vanish by balance, so some coefficient with $a,b\ge 1$ differs. The membership argument converts injective-profile inequality to homomorphism-profile inequality. This is the promised single polynomial-time reduction. ∎

## Consequences

Equation (1) on the diagonal also shows that equality of ordinary univariate independence polynomials on bipartite graphs is $\mathsf C_{=}\mathsf P$-complete under many-one reductions. Membership again follows from squaring the differences of the counts at each size. Taking *full graph complements* of the conflict graphs gives co-bipartite targets whose clique-size counts are the independence counts. Every homomorphism from a simple clique is injective. Thus clique homomorphism indistinguishability is many-one $\mathsf C_{=}\mathsf P$-complete even on those targets. The hardness constructions have large polynomial overhead and establish an asymptotic classification.

On bipartite target graphs, all connected cograph sources with an edge either are bicliques or have no homomorphism into the target. Connected bipartite cographs are complete bipartite, and any graph mapping into a bipartite graph inherits a bipartition. Disconnected sources contribute products over their connected components. Thus the same reduction proves many-one hardness for all-cograph homomorphism indistinguishability, equivalently the graph decision for two-dimensional dense Weisfeiler–Leman. On bipartite targets this decision is complete by the biclique membership argument. [Cograph characterization, Fact 7.2, and dense WL, Theorem 1.3](https://arxiv.org/html/2608.13382v1)
