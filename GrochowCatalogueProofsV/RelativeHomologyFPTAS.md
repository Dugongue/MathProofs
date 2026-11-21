# A deterministic FPTAS for binary relative homology localization

## GP-0999

Given an orientable triangulated surface of genus $g$ with any number of boundary components, a relative class in $H_1(S,\partial S;\mathbb F_2)$, and binary-encoded nonnegative rational edge weights, there is a deterministic $(1+\varepsilon)$-approximation algorithm for minimum-weight localization of the class. It also constructs a representative. Its running time is $4^g\operatorname{poly}(L,1/\varepsilon)$, where $L$ is the bit length of the full input. In particular there is an FPTAS at every fixed genus without any bound on the number of boundary components. The source problem uses binary homology. [Homology localization and weighted input model](https://doi.org/10.1007/s41468-025-00212-0)

### Relative chains as signed constraints

Represent the given relative cycle by coefficients $z_e\in\mathbb F_2$ on nonboundary edges. Boundary edges can be omitted in any relative representative, since their classes in the relative chain group are zero and weights are nonnegative. Relative boundaries come from the full space of face chains. For an interior edge $e$ incident to faces $u,v$, the coefficient of $e$ after adding such a boundary is $z_e+y_u+y_v$, where $y$ is the face-chain bit vector. Therefore the optimum is
$$
\min_{y}\sum_e w_e [\,y_u+y_v\ne z_e\,].
$$
Use the graph with one vertex per triangle and one edge joining the two triangles across each interior edge. It embeds in the original surface, so capping every boundary component supplies an embedding of genus at most $g$. Neither its size nor the genus bound grows with the number of relative-homology coordinates. If a graph embedding used below is noncellular, take the surface given by a regular neighborhood of the embedded graph and cap that neighborhood's boundary; this gives a cellular embedding of equal or smaller total genus, component by component. Loops, if present in a cellular map model, contribute constant penalties and can be handled separately.

### Exact optimization for small integral weights

For each signed edge of integral weight $w$, use $w$ internally disjoint paths between its endpoints, of length two if the desired relation is equality and of length three if it is inequality. They fit in a strip near the original embedded edge and yield a simple graph. If the endpoint bits have the desired parity, one can cut all edges on each path. Otherwise exactly one edge per path needs to be uncut. The internal vertices can be optimized independently, so maximizing the number of cut edges solves the integral-weight signed problem exactly.

For clarity, a deterministic $4^g\operatorname{poly}(M)$ algorithm for the resulting unweighted optimization follows from the Arf-invariant Pfaffian formula, where $M$ is the expanded graph size. For a graph $J$ with $v$ vertices and $m$ edges use its cut-count polynomial
$$
C_J(t)=\sum_{y\in\{0,1\}^v}t^{|\delta(y)|}.
$$
For $t\ne -1$ let $A=(1+t)/2$ and $B=(1-t)/(1+t)$. Write $\sigma_i=(-1)^{y_i}$ and expand edge factors $A(1+B\sigma_i\sigma_j)$. Summing over all spins cancels terms with any odd-degree vertex and gives
$$
C_J(t)=2^v A^m \sum_{\substack{F\subseteq E(J)\\F\text{ even}}}B^{|F|}.
$$
The even-subgraph polynomial for a graph embedded in an orientable surface of genus at most $g$ is evaluated by at most $4^g$ Pfaffians of a polynomial-size embedded gadget graph. The orientation data are found by binary face-parity equations and homology coordinates. Exact rational evaluation has polynomial bit cost per Pfaffian, because here the entries have polynomial bit length. Interpolate $C_J$ at the $m+1$ integers $1,\ldots,m+1$ and read its largest nonzero exponent. This yields the optimum value. [Loebl–Masbaum, constructive even-subgraph Pfaffian formula](https://arxiv.org/abs/0908.2925)

To obtain a witness without adding an external field, fix parities of original graph edges successively. Force a requested parity by adding $m+1$ additional private length-two or length-three paths beside that edge, choosing length by the requested parity. A correctly forced parity sacrifices zero uncut edges on these paths and an incorrectly forced one sacrifices at least $m+1$; this exceeds the entire original objective range. With earlier choices retained, recompute the least uncut value and compare it to the original optimum. Retain the trial parity if that optimum is achieved and the opposite parity otherwise. This maintains existence of an optimal assignment throughout. The parity of each original edge is then fixed and can be solved by binary linear equations to give an optimal labeling, and hence the desired representative. These supplementary paths preserve the genus bound and polynomial size.

### Rounding binary-encoded weights

Clear denominators using their product, which has polynomial bit length, so the positive weights become positive integers. Test whether all positive-weight parity constraints can be satisfied by a binary linear system. This handles optimum zero exactly. Otherwise if $m$ is the number of nonconstant constraints and $W=\sum_e w_e$, then $1\le \operatorname{OPT}\le W$. Try guesses $U=2^j$ for $0\le j\le\lceil\log_2 W\rceil$. Assume $0<\varepsilon\le1$. For a guess use $\delta=\varepsilon U/(2m)$ and round an edge to the integer weight
$$
\bar w_e=\min\!\left(\left\lfloor w_e/\delta\right\rfloor,\ \left\lfloor U/\delta\right\rfloor+1\right).
$$
All these weights are $O(m/\varepsilon)$, so the exact path expansion is polynomial. For a guess with $\operatorname{OPT}\le U<2\operatorname{OPT}$, an original optimal assignment has rounded cost at most $\lfloor U/\delta\rfloor$. An optimum of the rounded problem therefore violates no capped edge, since one such violation by itself costs more. Its original cost, after multiplying its rounded cost by $\delta$ and allowing less than $\delta$ per violated edge, is at most $\operatorname{OPT}+m\delta\le(1+\varepsilon)\operatorname{OPT}$. Return the best assignment found, measured in the original rational weights. There are polynomially many guesses, and any constant penalties omitted earlier can be added exactly. The witness face bits give the output relative cycle by adding the corresponding face boundary.

The face-variable reduction is the relative analogue of the earlier binary surface-homology and flat-constraint arguments. Here the boundary edges disappear in the relative chain group, so the embedded optimization graph retains genus $g$ while supporting arbitrarily many boundary components. [Prior surface localization](https://github.com/Dugongue/MathProofs/tree/f1a463ce1a77aa494b7d33b81a4cbaac5dcb708b/SurfaceHomologyLocalization)
