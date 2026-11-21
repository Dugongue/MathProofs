# Exact pole-cap region for sparse tensor powers

Fix the sparse Möbius-telescope pair \(T_m^+,T_m^-\) over any field \(k\) from [Sparse exponential poles](SparseSeed.md). Let \(\Gamma\) be its directed corner graph, including the identity corner \(x\to x\) at each vertex. A base cochain is an integer \(w(x,y)\) on these directed corners, with \(w(x,x)=0\). For every retained nonzero corner product \(xy\cdot yz=xz\), require \(w(x,z)-w(x,y)-w(y,z)=0\). On the one deleted product require the same expression to be an integer \(c(w)\ge1\).

For such a cochain form a directed graph with three copies \(A,B,C\) of the base vertices. For every corner \(x\to y\), use the three directed edges and rewards
\[
 B_x\longrightarrow A_y: \ w(x,y),\qquad
 A_x\longrightarrow C_y: \ w(x,y),\qquad
 C_y\longrightarrow B_x: \ -w(x,y).
\]
Any closed walk \(\gamma\) has length a multiple of \(3\). Let \(\rho(w)\) be the maximum, over nonempty closed walks, of total reward divided by \(|\gamma|/3\). The maximum is attained on a simple directed cycle. The identity corners give \(\rho(w)\ge0\). Define \(\lambda_m=\min_w\rho(w)\) over the base cochains just described.

**Theorem 1.** For all \(r\ge1\), the feasible nonnegative integer pole caps \((p_1,p_2,p_3)\) for arbitrary Laurent witnesses of \((T_m^+)^{\otimes r}\rightsquigarrow(T_m^-)^{\otimes r}\) are exactly
\[
 p_1+p_2+p_3\ \ge\ \lceil r\lambda_m\rceil .
\]
The right-hand side is also the minimum order of a polynomial-matrix degeneration. The number \(\lambda_m\) is attained, is rational with reduced denominator at most the number of vertices of \(\Gamma\), and can be computed by a finite search on the base graph alone.

The only earlier tensor-specific input is the cap extraction and diagonal sufficiency for arbitrary regrouped mode transformations proved in Sections 1–2 of [Amplification and cancellation](PowerSeed.md). The remainder computes the integer cap system exactly.

## 1. Fixed cochains and cycle means

Scalar powers of the parameter with exponents summing to zero redistribute the cap triple without changing the law. In particular the caps are equivalent to \((0,0,p)\) with \(p=p_1+p_2+p_3\). For these caps, the previously extracted inequalities say that on every corner
\[
  w(x,y)\le\alpha_x+\beta_x-\beta_y,\qquad
  w(x,y)\le\beta_x,\qquad
  w(x,y)\ge\alpha_x+\beta_x-p.
\]
The identity corners impose the diagonal inequalities \(\alpha_x,\beta_x\ge0\) and \(\alpha_x+\beta_x\le p\).

Fix an integer representative \(w_0\) and allow any gauge \(w(x,y)=w_0(x,y)+u_y-u_x\) with integer \(u_x\). With
\[
 C_x=u_x,\qquad A_x=u_x+\beta_x,\qquad B_x=u_x+\alpha_x+\beta_x,
\]
the cap system becomes
\[
 A_y-B_x\le-w_0(x,y),\quad C_y-A_x\le-w_0(x,y),\quad
 B_x-C_y\le p+w_0(x,y).
\]
Thus the arc costs are minus the listed rewards, plus \(p\) on every edge \(C_y\to B_x\). The system has a solution exactly when every directed cycle has nonnegative cost. Necessity is obtained by summing the inequalities. For sufficiency adjoin a new vertex with a zero-cost edge to every vertex and use its shortest-path distances as the potentials. If there are no negative cycles, deleting cycles from paths proves the minima exist. For integer \(p\) all costs and distances are integers. Thus the minimum cap sum in the gauge class is \(\lceil\rho(w_0)\rceil\). The reward of any cycle is invariant under a gauge because the three types of terms telescope along the cycle.

## 2. Splitting cochains on the regrouped product

The support graph for the power has tuples for vertices and one corner \(x\to y\) precisely when every \(x_i\to y_i\) is a base corner. Let \(w\) be any extracted integer cochain for the powered pair. Choose one reference tuple and restrict to its \(r\) coordinate fibers, obtaining base cochains \(w_i\). In the product, a simultaneous forward move on several coordinates is the composite of its single-coordinate moves, each step using an identity corner in the other coordinates. Every such composite is retained, so its weight is the sum of the step weights. Likewise the two routes around a square of moves in distinct coordinates have the same weight. Both assertions hold for signed walks by reversing any backward steps.

Consequently the difference
\[
 \delta(x,y)=w(x,y)-\sum_{i=1}^r w_i(x_i,y_i)
\]
has zero circulation on closed walks. It suffices to check walks starting at the reference tuple, since the underlying graph is connected. Subdivide simultaneous moves and commute adjacent steps in distinct coordinates, preserving their weight by the square identity. The sorted walk consists of loops on the reference coordinate fibers, and \(\delta\) is zero on every edge of each such fiber. Integrating \(\delta\) along a path from the reference to each vertex gives integer potentials \(u_x\), with \(\delta(x,y)=u_y-u_x\). Conversely, any sum of base cochains has the required product defects: each full defect is the sum of the defects of the coordinate products, a retained product has all zero defects, and a deleted product has at least one positive defect.

For the sum \(w_0=\sum_i w_i\), the layered graph of the power is the synchronous product of the base layered graphs. Each cycle projects to closed walks of the same length in the respective base graphs, so \(\rho(w_0)\le\sum_i \rho(w_i)\). Choose a maximizing directed cycle for each base, start each at a \(B\)-layer vertex, and repeat them to the least common multiple of their lengths. At each step the edge types agree. Hence the tuple walk exists and has mean reward \(\sum_i\rho(w_i)\), proving equality. This argument includes products having optimal witnesses whose gauges are defined on all tuples rather than as sums of vertex potentials on each factor.

Every feasible cap sum is therefore at least \(r\lambda_m\). Taking \(r\) copies of a minimizing base cochain and solving the product difference constraints at \(p=\lceil r\lambda_m\rceil\) yields integer potentials and hence a diagonal Laurent witness. Clearing the three caps gives a polynomial witness of order \(p\). Conversely, an order-\(p\) polynomial witness becomes a Laurent witness with cap triple \((0,0,p)\) by moving \(t^{-p}\) into the output matrix. This proves the asserted minimum for polynomial presentations.

For the finiteness assertion, choose an integer bound \(B\) supplied by any one base witness. If \(\rho(w)\le B\), the difference constraints at cap sum \(B\) gauge \(w\) to an integral representative with all weights in \([-B,B]\), by \(\beta_x\le B\) and \(\alpha_x+\beta_x\ge0\). Thus one may enumerate the bounded base cochains and evaluate their cycle means. A simple directed cycle in the three-layer graph uses at most \(|V(\Gamma)|\) edges of each type. This proves attainment and the stated denominator bound. For a fixed cochain the cycle mean can also be computed by standard maximum-cycle-mean algorithms. [Karp](https://doi.org/10.1016/0012-365X(78)90011-0)

In particular, if \(\lambda_m=a/b\) is in lowest terms, the minimum order increases by exactly \(a\) under \(r\mapsto r+b\). When \(b=1\) the one-copy minimum is additive at every power.

## 3. Joint pole and contact bounds

For an arbitrary Laurent witness, define its largest contact \(D_{\max}\) to be the greatest valuation of a generically nonzero, specially deleted product in the normalized associated graded corner law. Each corner line has a basis defined up to an integral unit. Hence changing its integral frame leaves this valuation unchanged. For an extracted cochain \(w\) the contact of a product is its defect \(w(x,z)-w(x,y)-w(y,z)\), by the earlier cap extraction.

**Theorem 2.** For integers \(p,D\ge0\), there is a witness for the \(r\)-th power with pole sum at most \(p\) and \(D_{\max}\le D\) if and only if there are \(r\) base cochains \(w_1,\ldots,w_r\) with
\[
 \sum_i \rho(w_i)\le p,\qquad \sum_i c(w_i)\le D.
\]
For any cochains satisfying these inequalities there is a monomial diagonal witness whose normalized image arc is polynomial of degree exactly \(\sum_i c(w_i)\). Thus the bound on intrinsic contact has a constructive polynomial image-degree consequence.

Indeed the product cochain decomposition preserves all defects, since a gauge has zero defect on any triangle. The defect at a given product is the sum of the defects of its coordinate products, each either zero or \(c(w_i)\). The maximum \(\sum_i c(w_i)\) is reached by taking the deleted base product in every coordinate. The pole optimization was proved in Sections 1–2. For the monomial witness every nonzero structure entry is its original coefficient multiplied by the corresponding power of the parameter, so the largest defect is exactly the normalized image degree.

The two-parameter region has an explicit rational polyhedral limit. Choose a contact-one base cochain of cap sum at most \(B\); the original punctured-cap cocycle supplies one. Let \(\mathcal S_m\) be the finite set of pairs \((\rho(w),c(w))\) from the bounded base search \(-B\le w(x,y)\le B\) with \(\rho(w)\le B\). Any pair from another cochain either occurs in this set by integral gauging, or has \(\rho(w)>B\) and is dominated coordinatewise by the contact-one pair. To test exact feasibility in Theorem 2, it therefore suffices to take \(r\) elements of \(\mathcal S_m\), with repetitions. The limiting normalized feasible region in coordinates \((p/r,D/r)\) is
\[
 \operatorname{conv}(\mathcal S_m)+\mathbb R_{\ge0}^2 .
\]
Every normalized feasible point belongs to this polyhedron. For any point of the polyhedron, approximate the convex coefficients of a representing combination by integer multiples of \(1/r\) summing to \(1\), then round each resulting budget upward to an integer. This gives feasible points above the specified point with coordinate errors bounded by a constant depending only on \(\mathcal S_m\), divided by \(r\). For a rational specified point one can choose rational coefficients, as the defining linear constraints are rational, and attain the point exactly at every multiple of a common denominator for the point and coefficients.

## 4. An exact strict rounding gap in the original family

Take \(m=1\), using the rank-then-lexicographic vertex labels of the barycentric subdivision of the cone on the three-edge boundary. Let \(0,1,2\) be the boundary vertices and \(3\) the cone apex. The original cap triangles are \(013,023,123\), with each string denoting its set of vertices. Order all simplex labels first by length and then lexicographically. Delete the flag \((3,03,013)\). The original support corners of the subdivided complex are the strict simplex inclusions and the ordering adds the missing successor edges.

Set \(w=-1\) on the original corners
\[
 03\to013,\qquad 0\to013,\qquad 0\to01
\]
and on the ordering corners \(0\to1,\ 03\to12,\ 023\to123\). Set all other weights to zero. The marked flag has defect \(1\). The only other flags incident to a nonzero original corner are \((0,03,013)\) and \((0,01,013)\), and their defects are zero.

Here is a rational potential certificate for \(\rho(w)\le1/2\). Set \(B_x=-1/2\) on \(\{0,03,023\}\), and \(A_x=C_x=-1/2\) on \(\{0,02,03,023\}\), with every remaining potential zero. On each negative edge \(B_x=-1/2\) and \(C_y=0\). On each zero edge, a vertex in the latter set maps to another vertex in it. These facts directly give the three inequalities from Section 1 at cap \(p=1/2\).

For every base cochain there is a closed layered walk using the reverse of the marked triangle. Start at \(B_3\), move forward to \(A_{013}\), use an identity step to \(C_{013}\), and move backward to \(B_{03}\). Use two identity steps to \(C_{03}\), then move backward to \(B_3\). Its total reward is the marked defect \(c(w)\ge1\) and its length is six. Therefore \(\lambda_1=1/2\) for these labels. The one-copy least order is \(1\), but the \(r\)-copy least order is exactly \(\lceil r/2\rceil\).

## Relation to earlier work

The earlier tensor-power result gives exact cap extraction and bounds of order \(r2^m\) for this family. The new optimization is the gauge reduction to a layered cycle mean and its exact behavior under synchronous powers. The finite linear program for asymptotic pole and contact caps uses the resulting base cycle means and integer contact types. Standard cycle-mean theory supplies a base-graph algorithm for each fixed cochain. Ganesh, Koiran and Oliveira give approximation-order bounds for different families determined by commuting normalized slices. [Amplification and cancellation](PowerSeed.md) [Karp](https://doi.org/10.1016/0012-365X(78)90011-0) [Ganesh–Koiran–Oliveira](https://arxiv.org/abs/2608.10179)

These are written proofs. The finite \(m=1\) potential certificate was also checked with exact integer difference constraints. The note has no Lean kernel verification.
