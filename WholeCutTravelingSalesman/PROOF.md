# Whole cut-polytope projections onto traveling salesman polytopes

Grochow's Open Question 5.4 asks whether an entire cut polytope on polynomially many vertices has the traveling salesman polytope as an affine image. The construction for a **face** of a cut polytope was given by Maksimenko. Below are a whole-polytope upper bound and lower bounds for several specified models of the map. The unrestricted polynomial-size question remains open. [Grochow, §§2, 5](https://theoryofcomputing.org/articles/v013a018/v013a018.pdf) · [Maksimenko, *Traveling salesman polytopes and cut polytopes*, Theorem 3](https://doi.org/10.1515/dma-2013-018)

## 1. Exact cube formulation and finite whole-polytope upper bound

Write \(\mathrm{CUT}_{m+1}\) for the complete-graph cut polytope. Orient each cut by placing a distinguished vertex \(0\) on the positive side. Write \(z_i\in\{-1,1\}\) for the side of vertex \(i\) and \(z_0=1\). The cut coordinates are \(\delta_{ij}=(1-z_i z_j)/2\) and \(\delta_{0i}=(1-z_i)/2\). Thus the restrictions of affine functions on \(\mathrm{CUT}_{m+1}\) to cut vertices are exactly the degree-at-most-two multilinear functions on the \(m\)-dimensional spin cube. An affine map onto a polytope \(P\) exists exactly when a vector-valued quadratic \(F\) sends every spin assignment into \(P\) and attains every vertex of \(P\). The criterion follows from preservation of convex combinations by affine maps.

Every \(k\)-vertex polytope is a whole-cut image using fewer than \(2k+1\) source vertices. Take \(m\) to be the least power of two at least \(k\), and take an \(m\)-by-\(m\) Sylvester Hadamard matrix \(H\), so \(HH^{\mathsf T}=H^{\mathsf T}H=mI\). For a spin assignment \(z\), set \(p_i(z)=((Hz)_i/m)^2\). These functions are nonnegative and sum to one, by \(z^{\mathsf T}H^{\mathsf T}Hz=m^2\). At a sign vector equal to row \(i\) of \(H\), they give exactly the \(i\)-th coordinate vector. Assign the first \(k\) rows to the \(k\) target vertices and assign every extra row to one of them. The resulting weighted convex combination gives the required map. For traveling salesman polytopes this bound is factorial in the number of cities.

The order \(m=O(k)\) is sharp for a \(k\)-vertex simplex. Under any surjection the \(k\) barycentric coordinates pull back to nonnegative quadratic functions \(p_i\) on the spin cube with sum one, each attaining one somewhere. On the uniform spin cube, degree-two hypercontractivity gives \(\|p_i\|_4\le3\|p_i\|_2\). Interpolating the second norm between the first and fourth gives \(\|p_i\|_2\le9\|p_i\|_1\). At any point the Fourier expansion and Cauchy-Schwarz give \(p_i(z)\le\sqrt{1+m+\binom{m}{2}}\|p_i\|_2\). Since the first norms of the nonnegative \(p_i\) sum to one, \(k\le9\sqrt{1+m+\binom{m}{2}}\). [Bonami inequality, O'Donnell, Chapter 9](https://www.cs.cmu.edu/~odonnell/papers/Analysis-of-Boolean-Functions-by-Ryan-ODonnell.pdf)

## 2. Low-treewidth whole-cut maps cannot suffice

For a vector-valued quadratic \(F\) on \(m\) spins, let \(G_F\) be the graph on the spin coordinates with \(ij\) an edge exactly when \(z_i z_j\) has a nonzero coefficient in at least one output coordinate. If \(G_F\) has treewidth \(t\), then

\[
\operatorname{xc}\bigl(\operatorname{conv} F(\{-1,1\}^m)\bigr)
\le (m+1)2^{t+1}.
\]

To prove this, choose a width-\(t\) tree decomposition and contract every tree edge for which one bag is contained in the other, retaining the larger bag. This still satisfies the running-intersection condition. In the resulting rooted tree, each nonroot bag has a vertex absent from its parent, and a single spin can be absent from the parent in this way in at most one bag. Otherwise its bags would fail to be connected. Thus there are at most \(m+1\) bags. Give each bag one probability variable for every sign assignment on the bag. Impose nonnegativity, normalization, and agreement of the full marginal distributions on every parent-child intersection.

These constraints are exact for the bag projections of distributions on the full cube. In one direction marginalizing a global distribution gives the constraints. For the other direction draw the root from its prescribed distribution and draw each child conditionally on the signs inherited on the intersection from its parent. Those signs already have the child's required intersection distribution, so this gives the child's full distribution. The running-intersection condition ensures all signs agree across bags. Every output monomial occurs in a bag, so its expectation is affine in the bag probabilities. This proves the displayed extension bound, since only nonnegativity contributes inequalities. This is the spin version of the marginal gluing step in the perfect-matching support-polytope proof.

Rothvoß's exponential extension-complexity lower bound now implies that a whole-cut map onto the traveling salesman polytope with polynomially many spin coordinates must have \(t=\Omega(n)\), where \(n\) is the number of cities. The directed polytope has the same lower bound because adding the two arc orientations projects it onto the symmetric polytope. [Rothvoß, Corollary 2](https://arxiv.org/abs/1311.2369)

## 3. A linear degree lower bound for the tour-incidence encoding

**Theorem.** Let \(\mathsf{STSP}_n\) be the symmetric traveling salesman polytope, with its coordinates indexed by the edges of \(K_n\), and let \(n\ge6\). Suppose a real polynomial map

\[
F : \{0,1\}^{E(K_n)}\longrightarrow \mathsf{STSP}_n
\]

fixes every Hamiltonian-cycle incidence vector in these same input coordinates. Then \(\deg F>(n-2)/2\). The same conclusion holds in the arc coordinates of the directed traveling salesman polytope for a map fixing all directed Hamiltonian-cycle incidence vectors.

**Proof for undirected cycles.** Multilinearize the polynomials on the Boolean cube. Average \(F\) under simultaneous relabeling of input and output cities by the full symmetric group. Convexity preserves containment in \(\mathsf{STSP}_n\), the average still fixes every tour, and the degree does not increase. We can therefore assume \(F\) is equivariant.

Fix distinct vertices \(u,v\). The polynomial \(F_{uv}\) is invariant under all permutations fixing \(u,v\) individually. It is a linear combination of orbit sums of squarefree edge monomials on at most \(d=\deg F\) edges. Each such orbit sum evaluated at a graph counts embeddings of a two-rooted graph with at most \(d\) edges, up to the constant automorphism factor of that rooted graph. In this translation the two root vertices are retained even when they are isolated in the monomial. Injective rooted homomorphism counts are linear combinations of ordinary rooted homomorphism counts of quotient patterns, by inclusion-exclusion over coincident pairs of pattern vertices. Quotients identifying the two distinct roots give zero. Quotients introducing loops also give zero. The other quotient patterns still have at most \(d\) edges after merging repeated edges.

We evaluate these ordinary counts on disjoint unions of simple cycles, each of length greater than \(d\), on the same \(n\) vertices. Orient each target cycle arbitrarily for purposes of counting displacements. For each connected component of a quotient pattern choose a spanning tree. Anchor one vertex in that component, at a prescribed root image if there is one. A homomorphism assigns a direction \(+1\) or \(-1\) to each oriented tree edge as it follows the target cycle. This gives integer displacements from the anchor. For a nontree edge, the spanning-tree path followed by that edge has length at most \(d\). Thus its consistency modulo the target cycle length is equivalent to consistency in the integers. With no prescribed root image there are \(n\) anchor images and the same number of integer completions for each. With exactly one root there is one fixed anchor, and its number is independent of its image.

If both roots lie in the same pattern component, anchor at the first. The number of completions with integer displacement \(s\) for the second is a constant depending on the pattern and \(s\), with \(|s|\le d\). If their images lie on different target cycles, there are no completions. If they lie on a target cycle of length \(L\), sum those constants over all \(s\in[-d,d]\) congruent to the target displacement modulo \(L\). There can be two such integers on a short target cycle. The sum is valid because a homomorphism uniquely specifies the sign of every oriented tree edge on a simple target cycle of length at least three. The other pattern components multiply the count by constants depending only on \(n\). Patterns whose roots lie in different components have a count independent of the target root positions.

Consequently, for a fixed output coordinate, there are real numbers \(\alpha,\beta_s\) such that on every such 2-factor

\[
F_{uv}=\alpha+\sum_{s\in I(u,v)}\beta_s ,
\]

where \(I(u,v)\) is the empty set when \(u,v\) lie in different target cycles and otherwise is the set of integers in \([-d,d]\) congruent to their signed displacement in their cycle. Since the roots have distinct images and each target cycle has length greater than \(d\), \(s=0\) makes no contribution.

A degree-zero map cannot fix all tours. Suppose \(d\ge1\) and \(n\ge2d+2\). On an \(n\)-cycle one may place the two roots at distance exceeding \(d\). Its set \(I(u,v)\) is empty, whence \(\alpha=0\). On an \(n\)-cycle the roots can also have displacement \(s\) for each nonzero \(s\in[-d,d]\), with that integer as the only contribution. For those cycles \(F_{uv}\) is the true edge indicator. Hence \(\beta_s=1\) for \(s=\pm1\) and \(\beta_s=0\) otherwise. For every 2-factor with cycle lengths greater than \(d\) the same formula now reads its edge indicator. No pair can have both \(+1\) and \(-1\) as contributions, since the cycles have length at least three.

Take a disconnected 2-factor with cycle lengths \(d+1\) and \(n-d-1\) when \(d\ge2\), and with cycle lengths \(3\) and \(n-3\) when \(d=1\). All lengths are at least three and greater than \(d\). The map fixes this 2-factor, which is impossible because the cut at one of its components has value zero and every Hamiltonian cycle crosses that cut at least twice. This proves the bound.

**Directed case.** Use directed edge monomials and ordered roots. In the homomorphism argument a directed pattern arc shifts the integer coordinate by \(+1\) along the target orientation, or by \(-1\) when traversed backwards. The same spanning-tree argument gives the formula for displacement contributions. Calibrating it on \(n\)-cycles gives \(\beta_s=1\) just for \(s=+1\) and gives \(\alpha=0\). Thus the map fixes the disconnected directed 2-factor, contradicting the outgoing cut inequality. \(\square\)

The theorem permits signed coefficients and fractional outputs everywhere away from the tour encodings. By Section 1, it rules out the direct tour-incidence choice of preimages in a whole-cut extension even when the affine map itself is otherwise unrestricted. Open Question 5.4 permits other preimages and additional spin coordinates.

## 4. A quantitative obstruction to integral or low-denominator pullbacks

A nonzero multilinear cube polynomial of degree at most \(d\) is nonzero on a fraction at least \(2^{-d}\) of assignments. One proof chooses a variable in a degree-\(d\) monomial. The difference of the two restrictions along this variable has degree at most \(d-1\) and is nonzero. Each nonzero value of the difference gives at least one nonzero value among the two original restrictions. Induction proves the claim.

Every edge coordinate of a whole-cut map onto \(\mathsf{STSP}_n\) is a nonzero quadratic, since some tour contains that edge and hence some cut maps to that tour. A uniform cut therefore has at least \(\binom n2/4\) nonzero target coordinates in expectation. If every cut image were a convex combination of at most \(r\) tours, its support would have size at most \(rn\). It follows that \(r\ge (n-1)/8\). If all coordinates at cut vertices lie in \(D^{-1}\mathbb{Z}\), then their nonnegativity and total sum \(n\) give the same support upper bound \(Dn\), forcing \(D\ge(n-1)/8\). In particular no integral affine map works for \(n\ge10\). The directed formulas give \(r,D\ge(n-1)/4\), using all \(n(n-1)\) possible arcs and the same total sum \(n\).

These bounds distinguish unrestricted affine maps from exponent-coordinate substitutions of the cut polynomial. They leave open the use of dense signed affine readouts with high-treewidth interaction graphs and arbitrary preimages of the tours.

## 5. Degree needed to give explicit mixture weights

Suppose a whole-cut map has an expression \(F(z)=\sum_T w_T(z)\mathbf1_T\), summing over all tours, in which every \(w_T\) is nonnegative on the cube, their sum there is one, and each \(w_T\) is a polynomial of degree at most \(D\). For an input whose image is a tour \(T'\), extremality forces \(w_T\) to equal one for \(T=T'\) and zero otherwise. Evaluating the functions on one representative input for each tour therefore gives the identity matrix. The functions are linearly independent in the space of degree-at-most-\(D\) multilinear cube polynomials. Consequently

\[
|\mathcal T|\le\sum_{j=0}^D\binom mj.
\]

If \(m\) is polynomial in \(n\), the factorial size of \(\mathcal T\) forces \(D=\Omega(n)\). In particular, the direct construction by individual quadratic weights cannot reach a polynomial number of spins for TSP. The condition here concerns the degrees of individual mixture weights. A general affine cut map only limits the degree of \(F\) itself.
