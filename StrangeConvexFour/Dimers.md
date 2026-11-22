# Tensor determinant balance from dimer occupation numbers

Let $F$ be an ordered field. A three-way tensor has rectangular middle support if its set of nonzero coordinates is

$$
S=\{(i,j,k):i\in I_j,\ k\in K_j\},
\qquad \varnothing\ne I_j\subseteq I,\quad \varnothing\ne K_j\subseteq K .
$$

All coordinates and slices are marked. Let $\mu=(u,v,w)$ be a positive integral vector of one-way marginals with common total $D$. Assume a real table of margins $\mu$ is positive at every point of $S$. The pair-support graphs $P$ and $Q$ have edges $ij$ for $i\in I_j$ and $jk$ for $k\in K_j$, respectively. Suppose they are planar. Their embeddings can be supplied or computed.

**Theorem.** There is a pair of scalar planar bipartite dimer graphs fixed by the support, embeddings and margins. For a positive tensor $x$ on $S$, compute the anchored within-slice $2\times2$ ratios, all pair-edge occupation means in the two graphs, and the product of their partition functions. These data are an exact fingerprint of the orbit of $x$ under positive diagonal transporters $g$ subject to $g^\mu=1$. Here $g^\mu$ is the weighted product of the entries of the three diagonal matrices, with exponents $\mu$. The occupation means are computable from two Kasteleyn matrices by determinant and inverse evaluation. For determinant-one diagonals in all three factors, take the uniform profile $D=L=\operatorname{lcm}(|I|,|J|,|K|)$, with margin $L/|I|, L/|J|, L/|K|$ at each vertex of its respective mode. Equality of the fingerprint and at most two positive power-membership tests classify the literal orbit over $F$. For signed tensors, apply the fingerprint to absolute values and solve a binary linear system for the signs. This gives deterministic polynomial bit time over the rationals in the uniform case and polynomially many field operations over an ordered field apart from the power tests. The scope is diagonal transport in the given coordinates, including determinant-one tensor transport with fixed ordered eigenspaces in each mode.

## A planar dimer graph for a pair of marginal vectors

Take a bipartite plane graph $G$, nonnegative prescribed integer degrees $b_v$, and integer edge capacities $0\le\ell_e\le\min(b_v,b_{v'})$ at the endpoints of $e$. For transportation without separate capacities, use equality in the upper bound. Replace each $e$ by $\ell_e$ parallel wires in its original corridor. At a vertex with $r$ wire endpoints and required degree $b$, use a gadget with $r$ ports on the same side of the bipartition, incident to the external wires in their given circular order. The gadget must admit an internal matching covering all vertices left after deleting a set of ports precisely when the deleted set has size $b$. An instance with $b>r$ is infeasible.

The following explicit grid realizes that signature. Put $m=r-b$. When $m=0$, use $r$ isolated ports. Otherwise take an $m$-row, $r$-column directed grid with east and south edges. Attach one source above each of the first $m$ columns, and one sink below every column. Any $m$ sinks with ordered columns $j_1<\cdots<j_m$ are reached by vertex-disjoint paths from the ordered sources. For the source in column $p$, go south to row $m-p+1$, east to column $j_p$, then south to its sink. The inequalities $j_p\ge p$ hold. When a path with a larger source index moves east, each smaller-index path is still to its left. When a smaller-index path moves east, each larger-index path has reached a column strictly to its right.

Replace each internal grid vertex by a white entrance and a black exit with an edge between them. A directed grid edge becomes an edge from its tail exit to its head entrance. Each source has only a black exit and each sink only a white entrance. Incoming grid edges are consecutive in the embedding, as are outgoing edges, so the splits preserve planarity. The sinks are the ports. If exactly $b$ ports are deleted, a disjoint family of directed paths to all remaining ports matches their vertices using the path edges. Use the internal entrance–exit edge at every unused grid vertex. Conversely, any internal perfect matching requires exactly $b$ deletions, by counting the two vertex colors. At vertices on the other side of the original bipartition, interchange the two port colors. The gadget fits in a disc and the external wires preserve their cyclic order.

Assign all internal edges weight one and all wires of an edge $e$ the weight $X_e$. Any perfect matching projects to its vector $H$ of wire counts, which is an integral transport of the prescribed margins. Conversely every feasible vector admits a choice of that many labeled wires on each edge and a matching in every gadget. The resulting partition polynomial is

$$
Z_G(X)=\sum_{H\text{ feasible}}\kappa_H X^H,\qquad \kappa_H\in\mathbb Z_{>0}.
$$

The integers $\kappa_H$ are the fiber sizes of the projection. The graph has $O(\sum_v(r_v+1)^2)$ vertices and edges. Its size is polynomial in $D+|E(G)|+|V(G)|$. The tensor's uniform total $L$ is at most $|I||J||K|$. Planarity-preserving $f$-factor gadgets and the corresponding minimum-cost flow reduction already appear in the earlier matching literature. The explicit grid here gives one implementation of the required positive support property. [Sankowski, ICALP 2018, full version §8 and Appendix E](https://arxiv.org/abs/1709.07869).

For positive activities the weighted matching law induces the transport law $\kappa_H X^H/Z_G(X)$. Its expected count on edge $e$ is

$$
M_G(X)_e=\frac{X_e}{Z_G(X)}\frac{\partial Z_G(X)}{\partial X_e}.
$$

A signed bipartite Kasteleyn matrix computes $Z_G$ up to a constant sign determined from a reference matching. The signing is chosen on the decorated graph and is independent of $X$. Since $Z_G(X)>0$ at positive $X$, the matrix is invertible. Differentiating its determinant gives the displayed mean as $X_e\operatorname{tr}(K^{-1}\partial K/\partial X_e)$. Each derivative uses the entries assigned to that edge's wires, so one inverse suffices. The determinant and occupation formula are classical. [Kasteleyn, *The Statistics of Dimers on a Lattice I*](https://doi.org/10.1016/0031-8914(61)90063-5) · [Kenyon, *Lectures on Dimers*, §3](https://arxiv.org/abs/0910.3129).

## First moments determine the gauge over an ordered field

Consider a finite set of integer vectors $H$ and positive constants $\kappa_h\in F$. For any positive weight vector $X$, write $p_X(h)=\kappa_h X^h/Z(X)$. If $p_X$ and $p_Y$ have the same vector mean, all ratios $X^h/Y^h$ are equal.

To prove this, put $R=X/Y$ coordinatewise. Subtract the means, express the difference as a double sum using $\sum_h p_X(h)=\sum_h p_Y(h)=1$, and pair the two orderings of each unordered pair. The result is a sum of positive multiples of differences $d=h-h'$ with $R^d>1$, equal to zero. Indeed the coefficient of each such oriented difference is $p_X(h)p_Y(h')-p_X(h')p_Y(h)>0$. If that finite set of differences were nonempty and its real convex hull contained zero, a rational convex combination would witness this, since the vectors are integral. Clearing denominators gives a nonzero nonnegative integer combination of the differences equal to zero. Multiplying the corresponding inequalities $R^d>1$ gives $1>1$ in $F$. Hence the real convex hull omits zero. A strictly separating real linear functional can be chosen rational because the inequalities are strict and finite in number. Evaluating it on the positive combination over the ordered field $F$ contradicts the combination's zero value. This proves the assertion. Constant ratios also imply equality of the laws and of their means. Over the real numbers the result is the usual injectivity of mean parametrization modulo affine relations. This proof uses only the ordered-field operations on the weights and rational separation on the exponent vectors. [Wainwright and Jordan, Proposition 3.2 and the appendix on exponential families](https://www2.cs.arizona.edu/~pachecoj/courses/csc665-1/papers/WainwrightJordan_TR2008.pdf).

For a pair transportation graph with the stated strict-feasibility promise, its feasible-table differences span the integer circulation lattice. Here is a short proof for the uncapacitated transportation problem used in the fingerprint. Every edge has an integral table using it, by integrality of bipartite transportation with prescribed integer margins. Sum one witness per edge to get a positive integer table of some multiple $m$ of the prescribed margins. It stays nonnegative after adding a unit signed fundamental cycle. A nonnegative integer table $T$ of margins $m$ times the base margins splits into $m$ base tables. The fractional table $T/m$ proves that the base transportation problem with integral upper bounds $T$ is feasible. Subtract an integral feasible solution and iterate. The original sum and the sum perturbed by a fundamental cycle both decompose this way. Their difference expresses the cycle in the desired integer span. Fundamental cycles generate all circulations.

By the first-moment result, equality of dimer means for positive $X,Y$ implies $(X/Y)^z=1$ on every signed fundamental cycle. Choose a spanning forest and propagate edge ratios to vertex multipliers, one of them fixed to one per component. The condition on every fundamental cycle ensures the resulting two endpoint multipliers multiply to the prescribed edge ratio on every edge. All factors lie in $F_{>0}$. Conversely every such vertex rescaling multiplies the weight of every table by the same factor because its marginals are fixed. Thus the first moment detects exactly the positive vertex gauge of either pair transportation problem.

## Tensor orbit reconstruction

Fix anchors $i_j\in I_j,k_j\in K_j$. Define

$$
A_{ij}(x)=x_{ij k_j},\qquad
B_{jk}(x)=x_{i_j j k}/x_{i_j j k_j},\qquad
C_{ijk}(x)=x_{ijk}/\bigl(A_{ij}(x)B_{jk}(x)\bigr).
$$

The entries $C_{ijk}$ are the anchored within-slice cross ratios. Use $A(x)$ as the activities for $P$ with prescribed margins $(u,v)$, and $B(x)$ as the activities for $Q$ with margins $(v,w)$. Positivity of a real tensor table on the support implies both pair transportation graphs have a positive real table. A diagonal transport $y_{ijk}=s_i t_j h_k x_{ijk}$ sends

$$
A_{ij}(y)/A_{ij}(x)=s_i t_j h_{k_j},\qquad
B_{jk}(y)/B_{jk}(x)=h_k/h_{k_j}.
$$

The cross ratios and the two vectors of means are unchanged. The partition mass $Z_P(A)Z_Q(B)$ is multiplied by $\prod_i s_i^{u_i}\prod_j t_j^{v_j}\prod_k h_k^{w_k}$; the two contributions involving $h_{k_j}^{v_j}$ cancel between the pair graphs.

Conversely, equality of the two vectors of means factors the ratio $A(y)/A(x)$ as $s_i\alpha_j$, and $B(y)/B(x)$ as $\beta_j h_k$, by the vertex gauge result. Equality of the cross ratios gives an ordinary diagonal transporter with middle factor $t_j=\alpha_j\beta_j$. The ratio of the two partition masses is its weighted character, so equality of the masses gives $g^\mu=1$. This proves the exact weighted orbit statement.

For the uniform profile, each component of the graph $P$ with $a'$ vertices in $I$ and $b'$ vertices in $J$ gives one positive stabilizer parameter. It multiplies the first-mode diagonals on this component by a common scalar and the corresponding middle-mode diagonals by its inverse. Its determinant exponent column is $(a',-b',0)$. Components of $Q$ give columns $(0,-b',c')$ in the same way. These parameters generate the ordinary diagonal stabilizer: comparing two triples inside the same rectangular slice forces equality on all outer entries connected by such overlaps, and then determines the middle diagonal entry. Uniform transportation forces the first column family to lie on the rational line of $(|I|,-|J|,0)$ and the second on the line of $(0,-|J|,|K|)$. Both occur. The determinant exponent matrix therefore has rank two. Integer Smith form applied multiplicatively to the inverse determinant tuple of the found transporter gives two power-membership tests. The third coordinate equals one by equality of the partition masses and the primitive relation $(L/|I|,L/|J|,L/|K|)$. A solution of the power tests supplies a stabilizer correction. Over a real-closed field every positive root exists. Over $\mathbb Q$, testing positive power membership amounts to exact integer root tests on the numerator and denominator in lowest terms.

For arbitrary signs, the sign factors and positive factors split multiplicatively over $F$. On the sign side, write $(-1)^\epsilon$ at each vertex and solve for the $\epsilon$'s over $\mathbb F_2$. Every supported triple adds one equation for its sign ratio. Determinant one adds an even-sum equation in each mode, and the weighted-character problem instead adds the single equation $\mu\cdot\epsilon=0$. Solutions on both sides give the desired signed transporter. With rational inputs, fraction-free determinant operations and exact rational linear algebra run in polynomial bit time in the decorated graph size and input bit lengths. The integer exponent matrix has polynomial size and admits polynomial-bit-time Smith form. The same dimer graph and fixed signing suffice for both tensors.

## A single determinant for a parameterized middle count

There is also a forward statistical-mechanical representation of the discrete-convex penalty curve. Fix integral outer margins $u,w$, and central bounds $0\le l_j\le v_j\le U_j$. Form the bipartite graph with vertex classes $I\sqcup J_{\rm out}$ and $J_{\rm in}\sqcup K$. Keep the pair edges and add one slack edge from $j_{\rm out}$ to $j_{\rm in}$ for each $j$. In this paragraph assume this whole split graph is planar. Give both vertices of each split pair prescribed degree $U_j$; retain the fixed outer degrees. Cap the slack edge by $U_j-l_j$. Its wire count is $s_j=U_j-v_j$: the degree equations at both ends force the same $v_j$ in the two pair transports. The supported vectors are precisely the feasible pairs of transports with the central bounds.

Let the pair flow costs be integral and $g_j(v_j)$ be integer-valued and discrete convex on the central domain. Rational costs can be scaled to this case by a common denominator. Weight every pair wire by $q$ to its linear cost. For the slack wires at $j$, use exponents equal to the successive increments of $s\mapsto g_j(U_j-s)$, starting at $s=0$. These increments are nondecreasing. For any prescribed slack count $s_j$, choosing the $s_j$ cheapest labeled wires realizes central cost $g_j(v_j)-g_j(U_j)$. Every such choice has a dimer extension by the grid construction. Mark one center $j_*$ by multiplying each of its slack weights by a second variable $z$. If $Z(q,z)$ is the resulting Laurent dimer partition polynomial and $V(t)$ the optimal total cost having $v_{j_*}=t$, then

$$
\min\deg_q\bigl([z^{U_{j_*}-t}]Z(q,z)\bigr)
=V(t)-\sum_j g_j(U_j).
$$

The coefficient vanishes exactly at infeasible counts. All matchings have positive multiplicities, so the least exponent cannot cancel. Adding a linear penalty $\lambda t$ is equivalent to minimizing these least exponents plus $\lambda t$. This identity gives the whole profile through one determinant, as a symbolic representation. The profile itself can be evaluated by integral min-cost flow when binary costs would make the written Laurent polynomial too large. Sankowski's minimum-cost flow reduction provides the underlying linear-degree construction; here the marking and convex slack increments preserve the entire coefficientwise minimum profile in one partition function.

The orbit theorem also applies if the two decorated dimer graphs have supplied cellular embeddings in closed orientable surfaces of genera $g_P,g_Q$. For each graph its partition polynomial is the Cimasoni–Reshetikhin signed sum of $4^g$ Pfaffians, with coefficients determined by Arf invariants of spin structures and a reference matching. The mean formula differentiates this polynomial identity. Pfaffian cofactors compute each derivative even if an individual summand vanishes at the supplied activities. The orbit proof then needs $O(4^{\max(g_P,g_Q)}\operatorname{poly}(N))$ field operations for the Pfaffian evaluations and derivatives, where $N$ is the decorated input size. [Cimasoni and Reshetikhin, *Dimers on Surface Graphs and Spin Structures I*, Theorem 5](https://doi.org/10.1007/s00220-007-0302-7).

## Verification and relationship to prior work

An exact finite check enumerated all port subsets at $1\le r\le6$ and $0\le b\le r$, counting local perfect matchings by a vertex-mask recursion. Exactly 126 of 768 subsets admitted local matchings, at precisely the required cardinalities. On a four-cycle with prescribed degree two everywhere and two labeled wires on every edge, the projected transport $H_{11}$ takes the values $0,1,2$, with gadget multiplicities $1,258,1$ for the chosen port orders. For cross ratio $\rho=X_{11}X_{22}/(X_{12}X_{21})$, its mean is $(258\rho+2\rho^2)/(1+258\rho+\rho^2)$. The control confirms that the inverse argument must allow nonuniform fiber sizes.

The local graph construction belongs to the established use of bipartite planar gadgets for degree-constrained matching and to the planar-network tradition for nonintersecting paths. Scalar realizations of multivalent local dimer systems also appear in higher-rank dimer work. The new scope proved here is the tensor orbit reconstruction from two marginal dimer laws and one mass product, its ordered-field inverse argument, and the use of a marked slack count to transport the convex penalty curve. The tensor part builds on the earlier rectangular-support invariant theorem, which uses exact transportation and a signed lattice to handle general fields. The special-linear target is the diagonal regime of Part III's determinant-constrained tensor question. [Postnikov, *Total Positivity, Grassmannians, and Networks*](https://arxiv.org/abs/math/0609764) · [Kenyon and Ovenhouse, *Higher-Rank Dimer Models*](https://arxiv.org/abs/2312.03087) · [Rectangular-support invariant theorem](https://github.com/Dugongue/MathProofs/blob/main/ParametricConvexFour/Tensor.md) · [Chen, Grochow, Qiao, Tang and Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135#S1.SS5).

Verification consists of written proofs and finite controls. Publication priority remains unconfirmed.
