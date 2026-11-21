# Torus null-cone tests and a circuit bound for flow weights

**GP-0754, monomial torus specialization.** Given an integer weight matrix $A$ for a diagonal complex torus action, the positive circuits of $A$ give a monomial family defining the null cone. The family has the least possible cardinality and the least sum of degrees among monomial invariant test families. It has a deterministic polynomial-size circuit encoding at fixed rank and can require exponentially many monomial tests at growing rank. For directed-flow weights of arbitrary rank, there is also a polynomial-size family of invariant circuits over the rationals.

## Proof

For weights $a_1,\ldots,a_n\in\mathbb Z^r$, a monomial $x^u$ is invariant exactly when $Au=0$. Define a positive circuit to be the inclusion-minimal support of a nonzero vector $u\in\mathbb R_{\ge0}^n$ satisfying $Au=0$. The null cone consists of points where every positive-degree invariant vanishes. This follows directly for tori: the invariant polynomials are sums of invariant monomials. If the origin belongs to the convex hull of the weights on the support of a point, a rational convex dependence gives a surviving positive-degree invariant monomial. If it does not belong, rational strict separation and rescaling give an integral one-parameter subgroup taking the point to the origin. A surviving monomial prevents that orbit-closure containment.

On a positive circuit $S$, the kernel of $A_S$ is one-dimensional. If there were a vector $v$ independent of a strictly positive kernel vector $u$, choose its sign to give a negative coordinate. Increase $t$ from zero in $u+tv$ up to the first zero coordinate. The resulting vector is nonnegative, nonzero by linear independence, and supported on a strict subset of $S$, a contradiction. The resulting kernel line has a unique primitive positive integer generator $u_S$ by rational row reduction. In particular $|S|-1=\mathrm{rank}(A_S)\le r$.

Every support admitting a nonnegative kernel vector contains a positive circuit, by finite minimization. It follows that $\{x^{u_S}\mid S\text{ a positive circuit}\}$ defines the null cone. Conversely, evaluate any monomial test family at the point whose coordinates on $S$ are 1 and all others are 0. The point is outside the null cone. A positive-degree test monomial must survive, so its support lies in $S$, and minimality forces its support to equal $S$. Its exponent vector is a positive integral multiple of $u_S$. This requirement holds separately for every circuit, proving both optimality claims.

For fixed rank enumerate subsets of size at most $r+1$, compute their rational kernels, and retain the one-dimensional kernels admitting a strictly positive vector. A one-dimensional kernel with a strictly positive vector plainly has minimal support, because every nonzero vector in that kernel has full support. Integer generator bit lengths are polynomial in the input length by determinant bounds, and each exponentiation is computable by repeated squaring. Thus the monomial family is represented by a deterministic polynomial-size list of arithmetic circuits.

For growing rank, on a directed cycle of $m\ge3$ vertices use two parallel arcs per segment, each with weight $e_i-e_{i+1}$ for segment $i$. A nonnegative kernel vector is a nonnegative balanced flow. Every nonzero such flow has positive total flow on each segment, and all the totals are equal. A minimal support therefore selects exactly one of the parallel arcs on each segment, and every such selection is minimal. This gives $2^m$ necessary monomial tests on $2m$ variables.

**Scope.** Optimality and the lower bound concern monomial test families. Polynomial tests or encodings that combine many monomials may have different complexity. [Garg, Ikenmeyer, Makam, Oliveira, Walter and Wigderson, Problem 15](https://www.math.ias.edu/~avi/PUBLICATIONS/LIPIcs-CCC-2020-12.pdf).

## Polynomially many invariant circuits for directed-flow actions

For a directed multigraph with $n$ edges and $r$ vertices, give the edge $e$ from $i$ to $j$ weight $e_i-e_j$. There is a family of at most $(n+1)r$ invariant polynomials defining this null cone, each with a circuit of size polynomial in $n+r$. The constants can be chosen rationally. This applies at arbitrary rank and permits several monomials per invariant.

Number the edges $0,\ldots,n-1$ and assemble the $r$-square matrix
$$
M_{ij}(x,t)=\sum_{e\text{ from }i\text{ to }j} x_e t^{2^e}.
$$
For $1\le a\le r$, let $P_a(x,t)$ be the coefficient of $z^a$ in $\det(I+zM(x,t))$. In the determinant expansion, every term of positive $z$-degree selects a vertex subset, a permutation on it, and one arc for each permutation step. Its selected edge set consists of vertex-disjoint directed cycles. Conversely such an edge set determines the subset, the permutation, and the arc choices uniquely. Its weight sum is zero and its coefficient is $1$ or $-1$. Distinct selected edge sets yield distinct powers of $t$, by binary expansion. Thus each $P_a$ is an invariant in $x$, and a directed simple cycle of length $a$ in the nonzero edge support makes $P_a(x,t)$ nonzero as a polynomial in $t$. The same argument covers loops as cycles of length 1.

An edge support admits a nonzero balanced nonnegative flow exactly when it contains a directed cycle. In the forward direction pick a positive-flow edge and walk along positive-flow edges, which always exist at each reached vertex by balance. Repetition in the finite graph yields a directed cycle. Consequently a point is outside the null cone exactly when at least one $P_a(x,t)$ is nonzero as a polynomial in $t$.

It remains to specialize $t$ simultaneously for every point. Let $U\subseteq\mathbb C^n$ be the complement of the null cone. Consider the incidence set of
$$
(x,t_1,\ldots,t_{n+1})\in U\times\mathbb C^{n+1}
$$
where $P_a(x,t_j)=0$ for every $a,j$. Its fibers over $U$ are finite, since for each $x$ at least one univariate polynomial in the list is nonzero. Its dimension is at most $n$ by the fiber dimension bound. The closure of its projection to the space of $t_1,\ldots,t_{n+1}$ has dimension at most $n$, so the complement contains a nonempty Zariski-open set. Rational tuples are Zariski dense, and any tuple in this open set gives the claimed invariant family. If $U$ is empty the conclusion holds with an empty test family.

With any fixed $t_j$, compute the scalars $t_j^{2^e}$ by repeated squaring. Each determinant evaluation in $z$ has an arithmetic circuit of polynomial size. Evaluating at $r+1$ distinct rational $z$-values and applying the corresponding linear interpolation gives the coefficient $P_a(x,t_j)$. Thus each test has a polynomial-size arithmetic circuit. The argument establishes nonuniform circuit size with rational constants and leaves a uniform selection algorithm and constant bit lengths open.

In particular the doubled-cycle example admits polynomially many invariant circuits while its monomial test count is exponential.
