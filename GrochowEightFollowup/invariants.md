# Moment-polytope obstructions for matching and an orbital criterion for symmetry-characterized graphs

## GP100: an exact description of the skew-edge moment model

Let \(G=(\{1,\ldots,n\},E)\) be a simple graph with \(E\ne\varnothing\) and even \(n\). Put \(V=\mathbb C^n\), and give
\[
   \mathcal V=\bigoplus_{e\in E}\bigwedge\nolimits^{2}V
\]
its standard orthogonal sum of Hermitian inner products. The reductive group
\(\mathrm{SL}(V)\times(\mathbb C^\times)^E\) acts by
\[
  (g,t)\cdot(u_e)_{e\in E}=(t_e(\bigwedge\nolimits^{2}g)u_e)_{e\in E}.
\]
Take the point \(v=(v_e)\) with \(v_{\{i,j\}}=e_i\wedge e_j\) for \(i<j\). The representation has dimension \(|E|\binom n2\). Intersect the projective moment polytope of the orbit closure of \([v]\) with the condition that the \(\mathrm{SL}(V)\) component is zero. The edge-torus coordinates \(p_e\), rescaled by \(x_e=np_e/2\), are **exactly**
\[
 \bigl\{x\in\mathbb R_{\ge0}^E: \ \sum_{e\ni i} x_e=1\ \text{for each }i\bigr\}.
\]
This is the fractional perfect matching polytope with just the degree constraints. In particular the nonabelian skew-edge construction fails to recover the Edmonds polytope, even relative to the standard affine identification of its edge weights. It works for bipartite inputs, where the degree-constraint matrix is totally unimodular. [Original moment-polytope question, challenge 4 in §9](https://arxiv.org/abs/1910.12375)

### Moment computation

At a representative \(u=(u_e)\) of squared norm one in the projective orbit closure, the edge-torus moment coordinates are \(p_e=\|u_e\|^2\). Each nonzero \(u_e\) is decomposable because the cone of decomposable bivectors is closed. Write \(P_e\) for the orthogonal projector to its two-plane. If \(u_e=\alpha a\wedge b\) for an orthonormal pair \(a,b\), then the infinitesimal action of a Hermitian matrix \(H\) on this bivector is \(\alpha(Ha\wedge b+a\wedge Hb)\). Pairing with \(u_e\) gives
\(\|u_e\|^2(\langle a,Ha\rangle+\langle b,Hb\rangle)=p_e\operatorname{tr}(HP_e)\). The condition that the moment vanish on all traceless Hermitian \(H\) is therefore
\[
        \sum_{p_e>0}p_eP_e=\frac{2}{n}I.
\]
The coefficient on the right follows from the trace. These formulas choose a moment convention without an overall common scale.

### Orbit-closure constraints and attainment

Choose orbit points \((g_j,t^{(j)})[v]\) converging to \([u]\). The complex projective orbit is constructible, and its complex-topology closure agrees with its Zariski closure, so such a sequence exists for every point considered. After one subsequence, all lines \(\mathbb Cg_je_i\) converge in projective space to lines \(\ell_i\). For every fixed edge \(e\) with positive \(p_e\), its two-plane at the \(j\)-th orbit point converges to the plane of \(u_e\). If \(i\in e\) then it contains \(\mathbb Cg_je_i\) at each step and thus contains \(\ell_i\) in the limit. The incidence of a line and a containing plane is closed.

Fix a unit vector \(b_i\) on \(\ell_i\) and evaluate the zero-moment equation on it. The expectation of each \(P_e\) is nonnegative and is one on every positive-weight edge incident to \(i\). Thus \(\sum_{e\ni i}p_e\le 2/n\). Equality must hold for each \(i\) because the sum over all vertices is \(2\sum_e p_e=2\). Conversely, given these equalities, take \(u_e=\sqrt{p_e}\,v_e\). This is an orbit point if all \(p_e>0\), and otherwise a limit obtained by taking the zero edge scalars to zero. Its projectors are the original coordinate two-plane projectors and the equalities give zero moment. This proves both inclusions, including boundary points and graphs with empty zero moment fiber.

For example, in the graph of two disjoint triangles, giving their six edges weight \(1/2\) meets every degree constraint even though a perfect matching does not exist. The same weights extended by zero to \(K_6\) give a point of this moment fiber excluded by an odd-cut inequality of the nonempty perfect matching polytope of \(K_6\).

## An exact compact spectral model of the perfect matching polytope

Let \(\mathcal U(G)\) be the set of skew-symmetric unitary \(n\times n\) matrices \(U\) over \(\mathbb C\) supported on \(E\), so \(U_{ji}=-U_{ij}\) and \(U_{ij}=0\) for nonedges. Define \(w(U)_{\{i,j\}}=|U_{ij}|^2\). Then
\[
        \operatorname{conv}\{w(U):U\in\mathcal U(G)\}
               =\mathrm{PM}(G).
\]
A point \(w(U)\) satisfies nonnegativity and the degree equations because the rows of \(U\) have norm one. For an odd vertex set \(S\), its principal block \(U_{S,S}\) is singular: transpose negation gives a determinant equal to its own negative. Take a unit kernel vector \(a\) supported on \(S\). Unitarity gives \(\|U_{S^c,S}a\|^2=1\), and the squared Frobenius norm bounds the squared norm on every unit vector. Thus
\[
    \sum_{e\in\delta(S)} w(U)_e=\|U_{S^c,S}\|_{\mathrm F}^2\ge1.
\]
Edmonds' inequalities give \(w(U)\in\mathrm{PM}(G)\). In the other direction, a perfect matching gives a supported skew unitary by putting the block \(\left(\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right)\) on each matched pair. Its squared entries give precisely the matching incidence vector. This proof covers graphs without a perfect matching as well, since then both sets are empty. [Edmonds' matching polytope theorem](https://doi.org/10.6028/JRES.069B.013)

Equivalently, start with the **single** coherent skew form \(\omega=\sum_{i<j}u_{ij}e_i\wedge e_j\) and its skew coefficient matrix \(U\). On projective space the \(\mathrm{SL}(V)\) moment is proportional to the traceless part of \(UU^*\), and the standard coordinate-torus moments are proportional to the edge weights \(|u_{ij}|^2\). The first formula follows by the infinitesimal action \(H\cdot U=HU+UH^T\), using skew symmetry in the Frobenius inner product. Hence the Edmonds polytope is the convex hull of the edge-torus moment of the **supported, \(\mathrm{SL}(V)\)-balanced locus**, with the same \(n/2\) rescaling of the normalized edge coordinates as above. This uses matrices of dimension \(n\), with \(O(n^2)\) variables. The independently acting torus of the direct-sum construction commutes with \(\mathrm{SL}(V)\). Here coordinate rephasing on a single skew form generally fails to preserve the joint balanced locus, so this construction does not assert a realization as a moment polytope of one commuting product action on an orbit closure.

Convexification is essential in this model. In a six-cycle the weight \(1/2\) on each edge is the midpoint of its two perfect matchings. The rows corresponding to vertices at distance two share exactly one nonzero column under this support and weight, and that single nonzero term cannot give an inner product of zero. Thus the midpoint is not itself \(w(U)\).

## GP100: an extension-complexity obstruction for spectral-sum constructions

A second obstruction covers arbitrary compositions of the following building blocks. Each spectral block has ports \((\lambda,\mu,\nu)\) of length \(d\), with membership meaning that they are the decreasing eigenvalue lists of Hermitian matrices \(A,B,A+B\). Fixed spectra are imposed by affine equalities. Additional blocks may be any polytopes or polyhedral cones supplied with explicit linear lifts. The outputs are affine images of the feasible port values. Blocks may share, duplicate, or identify ports by affine equations, and the construction may add explicit affine inequalities. A fixed-spectrum Hermitian sum is the moment map for the diagonal action on a product of type-\(A\) coadjoint orbits, so this class includes general networks of these nonabelian moment-polytope operations. It also includes spectral sums of more than two matrices by chaining ports for partial-sum spectra. For the latter statement, each subsequent pair can be jointly conjugated to identify its incoming matrix with the preceding partial sum of the same spectrum.

Let the spectral block orders be \(d_1,\ldots,d_s\), let \(b\) be the number of added linear inequalities, and let the additional blocks have lifts with a total of \(c\) inequalities. The output, if bounded, has extension complexity at most
\[
                C\sum_{i=1}^s d_i^2+b+c
\]
for an absolute constant \(C\). Indeed, by the real honeycomb or hive theorem the spectral-sum relation is the projection of a triangular hive array with \(\binom{d+2}{2}\) entries, one linear inequality per elementary rhombus, and equations reading the three boundary differences. At most \(O(d^2)\) inequalities are needed, including ordering if imposed separately. Introduce an independent hive for each block. Their constraints, the additional lifts, and the affine constraints already in the construction form one linear lift of the exact output. Affine projection and slicing only use equations. This argument counts inequalities in a polyhedral lift. It also gives the same lower-bound conclusion for formulations that require a bounded extension, by the standard equivalence with nonnegative slack-matrix factorizations. [Knutson–Tao's honeycomb theorem](https://arxiv.org/abs/math/0009048) · [Real-hive statement](https://doi.org/10.1016/j.aim.2017.01.006)

Rothvoß proved that \(\operatorname{xc}(\mathrm{PM}(K_{2r}))=2^{\Omega(r)}\), where \(\mathrm{PM}\) denotes the perfect matching polytope. Consequently every construction of the indicated type for this family has
\(\sum_i d_i^2+b+c\ge 2^{\Omega(r)}\). This conclusion allows arbitrary real constants and affine projections. The bound resolves the specified-natural-class obstruction branch of GP100 for the spectral-sum constructions, and the preceding theorem resolves it for the skew-edge construction. The question for unrestricted reductive representations and distinguished orbit closures remains open. [Rothvoß's lower bound](https://arxiv.org/abs/1311.2369)

## An exact orbital criterion for GP071

Use the definition of symmetry characterization in Grochow–Urisman. A graph \(X\) on the same vertex set as \(G\) that is invariant under every element of \(\operatorname{Aut}(G)\) must be isomorphic to \(G\), to its complement, or to a trivial graph. Let \(O_1,\ldots,O_r\) be the orbits of \(\operatorname{Aut}(G)\) on **unordered** vertex pairs. The following criterion holds for every simple graph.

- If \(r\le 2\), the graph is characterized by its symmetries.
- If \(r=3\), it is characterized exactly when the three graphs with edge sets \(O_1,O_2,O_3\) are mutually isomorphic.
- If \(r\ge 4\), it is never characterized.

Every invariant graph has edge set a union of the pair orbits. Let \(m=|E(G)|\) and \(N=\binom n2\). A graph allowed by the definition has edge count in \(\{0,m,N-m,N\}\). For any ordering of the \(r\) orbits, the size of the union of each prefix is strictly increasing, so \(r+1\le4\) if \(G\) is characterized. If \(r=3\), the allowed edge counts must all be distinct and the two intermediate prefix unions must have the respective smaller and larger nontrivial counts. Any orbit can be first, so all three single-orbit graphs have the smaller count and each is isomorphic to the unique one among \(G,\bar G\) with that count. Conversely, if all three single-orbit graphs are isomorphic, each union of two orbits is the complement of the third. The graph \(G\) is one of these nontrivial unions, so the criterion gives exactly the allowed list. If \(r\le2\), the only nontrivial invariant graphs, if any, have complementary edge sets. [Definition and recognition question](https://arxiv.org/html/2606.26244v2#S1.SS3)

This criterion also contradicts the rank-three sentence preceding Open Question 1.9 in that version. The seven-cycle \(C_7\) has full automorphism group the dihedral group acting on the cycle, so the pair-orbits consist of cyclic distances \(1,2,3\). Each single-orbit graph is a \(C_7\) because each nonzero step generates the group of residues modulo seven. Every ordered orbital off the diagonal is symmetric under reversing its endpoints. Hence the permutation rank is four, even though this graph is symmetry-characterized and is neither trivial, a star, nor the complement of a star.

### Recognition complexity

The criterion gives a deterministic polynomial-time Turing reduction to graph isomorphism. Test whether two supplied unordered pairs are in the same orbit by marking the pairs with a vertex color and asking colored graph isomorphism. Comparing each unordered pair to a list of at most three representatives yields all orbits or rejects on finding a fourth. Colored graph isomorphism reduces to ordinary graph isomorphism by attaching distinguishable color gadgets. For the three-orbit case, compare the three orbital graphs. There are \(O(n^2)\) oracle calls.

The recognition language also lies in \(\mathrm{NP}\cap\mathrm{coAM}\). For the NP verification, give generators of a subgroup \(H\) of graph automorphisms and any isomorphisms needed by the criterion on its orbits. Each generator is checked directly, and its action on the at most \(\binom n2\) pairs lets one compute the orbits of \(H\) by graph traversal. If the required condition holds for \(H\), it holds for the full group, since a graph invariant under the full group is also invariant under \(H\). On yes instances one may take generators for the full group, whose generating set size is at most \(\log_2(n!)\), by successively doubling the generated subgroup.

For the \(\mathrm{coAM}\) bound, a no instance has a disqualifying graph \(X\). This graph is nontrivial and is not isomorphic to \(G\) or \(\bar G\), and no unordered edge of \(X\) is in the same \(\operatorname{Aut}(G)\)-orbit as an unordered nonedge of \(X\). The latter condition is a list of at most \(N^2\) colored graph nonisomorphism tests, using the two pair markings described above. Conversely those conditions certify exactly that \(X\) is disqualifying. Use the public-coin AM protocol for graph nonisomorphism and amplify the error of each test below \(2^{-2N-10}/(N+2)^2\) before running the tests in parallel. For any fixed invalid \(X\), at least one condition is false, so the probability of a successful transcript is at most this soundness error. A union bound over the at most \(2^N\) choices of \(X\) preserves soundness even if Merlin chooses \(X\) after seeing the public coins. For a valid \(X\), completeness follows by a union bound over its polynomially many tests. [Goldreich–Micali–Wigderson, graph nonisomorphism protocol](https://doi.org/10.1145/116825.116852) · [Goldwasser–Sipser, public coins](https://doi.org/10.1145/12130.12137)

This addresses recognition with an exact structural criterion and complexity upper bounds. Deterministic polynomial-time recognition and the related promise-isomorphism problem remain open. The results in this file are paper proofs.
