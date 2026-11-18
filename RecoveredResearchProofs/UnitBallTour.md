# A base-two approximation for Euclidean TSP with unit-ball neighborhoods

**Theorem.** For every fixed dimension $d\geq2$, a polynomial-time algorithm finds a closed tour meeting every ball in an arbitrary finite collection of closed unit balls in $\mathbb R^d$. Its length is at most $O(d^{3/2}\log(d+1)\,2^d)$ times optimum, with an absolute constant. The balls may overlap and the guarantee applies even when the optimum is arbitrarily short.

This is an informal proof recovered from the August 2026 research notes. The original observation replaces a half-angle packing by a direct spherical covering in Dumitrescu and Tóth's construction. A short-tour case supplied here removes an additive term in the archived bound. The theorem improves the exponential base in their arbitrary-dimensional estimate. The dimension-independent or subexponential approximation direction mentioned by Bercea remains open in this proof. A 2025 PTAS independently covers the planar case. [Dumitrescu–Tóth, Theorem 5](https://arxiv.org/abs/1303.6659) · [Bercea, Introduction](https://arxiv.org/html/1809.07159#S1) · [Bandyapadhyay et al., SODA 2025](https://doi.org/10.1137/1.9781611978322.78)

## A finite spherical covering

Take unit directions $U\subset S^{d-1}$ whose closed angular caps of radius $\pi/6$ cover the unit sphere. Böröczky and Wintsche's equal-cap covering theorem permits
$$
 |U|=O(d^{3/2}\log(d+1)\,2^d).
$$
The same cardinality bound holds with radius $\pi/6-c/d$ for any sufficiently small absolute $c>0$, because $\sin(\pi/6-c/d)^{-(d-1)}=O(2^d)$. This leaves slack to choose rational unit directions, which are dense by stereographic projection. For a fixed dimension, the directions can be precomputed deterministically. Enumerate finite lists of rational unit directions with increasing description length and test covering by quantifier elimination on the unit sphere using threshold $\sqrt3/2$. Stop at a list satisfying the cardinality bound, with any sufficiently large absolute constant from the covering theorem. The strict-radius existence argument ensures termination. Precomputation depends only on $d$. [Böröczky–Wintsche, Corollary 1.2](https://doi.org/10.1007/978-3-642-55566-4_10)

For a representative ball centered at $o$, consider the points $o$ and $o+\sqrt3 u$ for $u\in U$. Any unit ball intersecting the representative ball contains one of these points. Indeed, its center $x$ has distance $t\leq2$ from $o$. If $t\leq1$ the point $o$ suffices. Otherwise choose $u$ with $\langle u,x-o\rangle\geq(\sqrt3/2)t$. Then
$$
 \|x-(o+\sqrt3 u)\|^2\leq t^2+3-3t\leq1
$$
for $1\leq t\leq2$. A closed detour from $o$ through the listed points has length at most $2\sqrt3|U|$, by returning to $o$ after each point. This bound needs no adjacency among the points of the covering.

## A bound for separated representatives

In any dimension, a ball of radius less than $2/\sqrt3$ contains at most two points with pairwise distances at least 2. For three such points their average squared distance to their centroid is the sum of their three squared pairwise distances divided by 9, hence is at least $4/3$. The average squared distance to any other point is at least as large.

Let an optimal tour have length $L^*$ and let $k$ pairwise disjoint unit balls meet it. Split the tour into arcs of length at most $1/4$. Each arc lies within $1/8$ of its arclength midpoint. The centers of the selected balls assigned to an arc therefore lie within $9/8<2/\sqrt3$ of that midpoint. There are at most two such centers per arc, so $k\leq8L^*+2$, with the constant-tour case immediate. Dimension-independent packing estimates were already implicit in the earlier work cited below. [Qi–Qi–Chen, SoCG 2023](https://arxiv.org/abs/2303.06759)

Greedily choose a maximal pairwise disjoint family. Each input ball intersects a representative. The optimal tour can visit the $k$ representative centers via excursions of total length at most $2k$. A doubled Euclidean minimum spanning tree therefore gives a closed center tour of length at most $2(L^*+2k)$, including when there is just one center. Insert the spherical-covering detour at each representative. The output length is at most
$$
 2L^*+4k+2\sqrt3|U|k.
$$
Thus whenever $L^*\geq1/5$, this gives a multiplicative bound $O(|U|)$.

## The short-tour case

Let $o$ be the center of the minimum enclosing ball of the input centers and write its radius as $r$. Every point on an optimal closed tour is within arclength $L^*/2$ of a visit to any particular ball. Therefore $r\leq1+L^*/2$. If $r\leq1$, output the point $o$. If $r>11/10$, then $L^*>1/5$ and the previous branch applies.

In the remaining case put $\delta=r-1\in(0,1/10]$. Take $o$ and the points $o+2\delta u$ for $u\in U$. A ball whose center $x$ is at distance $t\leq1$ from $o$ is already covered. For $1<t\leq1+\delta$, choose $u$ with $\langle u,x-o\rangle\geq(\sqrt3/2)t$. Then
$$
\begin{aligned}
 \|x-(o+2\delta u)\|^2-1
 &\leq t^2-1+4\delta^2-2\sqrt3\delta t\\
 &\leq \delta(2+5\delta-2\sqrt3)<0.
\end{aligned}
$$
Returning to $o$ after each visit gives total length at most $4\delta|U|\leq2L^*|U|$. This is the required bound with no additive overhead.

All work after precomputation is polynomial. A minimum enclosing ball can be found by testing the affine circumcenters of affinely independent subsets of at most $d+1$ input centers and keeping the smallest enclosing candidate. Such a subset supports a minimum enclosing ball, since its center belongs to the convex hull of its boundary centers, and Carathéodory's theorem applies. All scalar comparisons and point coordinates have polynomial-size exact algebraic representations for rational input and fixed $d$. The greedy family, spanning tree and detours therefore give the claimed deterministic algorithm.
