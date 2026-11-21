# Determinant-resolved isomorphism of cubic graph tensors

Chen, Grochow, Qiao, Tang and Zhang ask whether special-linear tensor isomorphism reduces to general-linear tensor isomorphism and whether the corresponding complexity classes agree. Their question concerns arbitrary tensors. The result here resolves decision, counting and witness construction for an explicitly presented family of graph tensors. The reduction works by recovering three coordinate frames and then solving at most two nontrivial scalar power equations for each candidate graph isomorphism. [Open Question 1.9](https://arxiv.org/pdf/2306.03135#page=10)

## Theorem

Let \(G,H\) be connected simple cubic graphs with no four-cycle. Each graph has a proper edge-colouring with three labelled colours \(A,B,C\) and a specified order on the edges of each colour. Over a field \(K\), give every vertex a nonzero weight and form

\[
T(G,w)=\sum_{v\in V(G)} w(v)e_{a(v)}\otimes e_{b(v)}\otimes e_{c(v)},
\]

where \(a(v),b(v),c(v)\) are the incident edges in the three colours. Define \(T(H,z)\) the same way. For any prescribed \((\delta_A,\delta_B,\delta_C)\in (K^\times)^3\), all transporters with these three determinants are described by the tests below. There are at most \(|V(H)|\) candidate maps, one for each image of a fixed root of \(G\). For each candidate, the tests are scalar equalities and at most two equations \(x^s=b\) with \(s=O(|V(G)|^2)\). Each solution of the scalar system gives one transporter, and the parametrization records every transporter exactly once.

Over an explicitly represented finite field \(K=\mathbb F_q\), decision and exact counting take deterministic time polynomial in the input length, including \(\log q\). A witness can be produced in expected polynomial time by finite-field polynomial factorization. For each fixed finite field, exhaustive search for the at most two scalar roots also gives deterministic polynomial-time witness construction. Setting all three determinants to one gives the special-linear problem on this family.

## Recovering the graph

The following rank argument is the recovery step from the earlier weighted cubic-graph tensor result. Fix colour \(A\) and contract in its dual by \(x\). For every vertex incident with an \(A\)-edge on which \(x\) is nonzero, the slice has a nonzero entry at \((b(v),c(v))\). Distinct vertices cannot give the same entry in a simple graph. The bipartite graph of nonzero entries has degree at most two, and the components are paths or even cycles. Its four-cycles would give four-cycles in \(G\), so its cycles have length at least six. A path with \(ell\) edges has slice rank \(\lceil\ell/2\rceil\). A largest matching gives a nonzero minor because the selected subgraph is a forest, and the smaller side has that cardinality. A cycle with \(2k\) edges has rank at least \(k-1\), by deleting adjacent row and column vertices and taking the matching minor in the remaining path. The total rank is the sum over the components.

One selected \(A\)-edge gives two disjoint nonzero entries, hence rank two. Four or more selected \(A\)-edges give at least eight matrix edges, each component contributing at least one third of its edge count to the rank, so the rank is at least three. Three selected \(A\)-edges give six matrix edges. If the support is a forest the rank is at least three. Otherwise it is a six-cycle, which corresponds to a two-colour six-cycle in \(G\). The three selected \(A\)-edges would match its vertices by chords. Consecutive endpoints are excluded by simplicity, and distance-three chords are excluded by the four-cycle condition. Distance-two chords stay in two classes of odd size and cannot form a perfect matching. Finally, two selected \(A\)-edges give four matrix edges. Rank at most two forces every path component size to be even. For two paths of length two, the two remaining-colour adjacencies form a matching on the four original vertices, disjoint from the \(A\)-matching. The union is a four-cycle. For one path of length four, label its four matrix edges in order. The only matching of these four labels disjoint from the consecutive adjacencies is \(13,24\), which gives a four-cycle using adjacencies \(12,34\).

Thus the rank-two contractions in each factor are exactly the nonzero vectors on its dual coordinate lines. Tensor transport preserves contraction ranks, so an invertible transporter permutes those lines in each factor and is monomial. Permuting coordinates transports support triples, which identify the original vertices. Two vertices share an edge of colour \(c\) exactly when their triples agree in coordinate \(c\). The induced permutations therefore come from a colour-preserving graph isomorphism \(\phi\). Its image on one vertex determines it by propagation along the unique incident edge of each colour. Testing consistency and bijectivity for all root images enumerates every such map in polynomial time.

## Scalars and determinants

Fix a passing graph map \(\phi\). For every edge \(e\) let \(\lambda_e\in K^\times\) be the scalar used to map its basis vector to the basis vector of \(\phi(e)\). Let \(\sigma_c\in K^\times\) be the sign of the induced colour-\(c\) permutation in the specified basis orders. Set

\[
r_v=\frac{z(\phi(v))}{w(v)},\qquad b_c=\delta_c/\sigma_c.
\]

The equations are exactly

\[
\prod_{e\ni v}\lambda_e=r_v,\qquad
\prod_{e\in E_c(G)}\lambda_e=b_c.
\tag{1}
\]

The first equations match the coefficients on all supported triples. The second equations are the determinant formula for a monomial matrix. Conversely, any solution of (1) supplies the three invertible monomial matrices and satisfies the determinant requirements. Distinct graph maps or scalar assignments supply distinct transporters.

## Two power equations suffice

Let \(M\) have one row for each vertex and one for each colour, with one column per edge. The column of an edge \(uv\) of colour \(c\) has a one in rows \(u,v,c\) and zero elsewhere. Thus \(M\) presents the monomial homomorphism in (1). Equivalently, its cokernel has generators \(u_v,t_c\) with one relation \(u_v+u_w+t_c=0\) per edge \(vw\).

Choose a rooted spanning tree, with root \(o\). Each tree relation solves for its child generator with coefficient one. Eliminating the child generators gives \(n-1\) unit pivots and leaves four generators \(u_o,t_A,t_B,t_C\), where \(n=|V(G)|\). In the remaining relations write

\[
u_v=\epsilon_v u_o + \alpha_{v,A} t_A+\alpha_{v,B}t_B+\alpha_{v,C}t_C,
\qquad \epsilon_v=(-1)^{\operatorname{dist}(o,v)}.
\]

At the root \(\alpha_o=0\). A tree edge of colour \(c\) from parent \(u\) to child \(v\) gives \(\alpha_v=-\alpha_u-e_c\). In particular \(\sum_c\alpha_{v,c}=(\epsilon_v-1)/2\), and each coefficient has magnitude at most \(n-1\). For a chord \(uv\) of colour \(c\), let \(a=\alpha_u+\alpha_v+e_c\) and \(\beta=(\epsilon_u+\epsilon_v)/2\). Then \(\sum_c a_c=\beta\) and the chord relation is

\[
a_A(t_A-t_C)+a_B(t_B-t_C)+\beta(2u_o+t_C)=0.
\tag{2}
\]

The two differences and the displayed combination, together with \(u_o\), form a unimodular basis. If the graph is bipartite, every chord has \(\beta=0\). Otherwise there is a chord with equal endpoint parity, whose \(\beta\) is \(1\) or \(-1\). This coefficient is a unit, so that chord eliminates \(2u_o+t_C\) using one more unit pivot. In both cases the remaining matrix has only two possibly nonzero rows. Its entries have magnitude \(O(n)\), including after the possible extra elimination, which subtracts at most one signed copy of the pivot relation from each other relation. This proves that at most two nonzero Smith diagonals exceed one. If the residual rank is two, the product of its two positive Smith diagonals divides each nonzero two-by-two minor, all of magnitude \(O(n^2)\). At residual rank one the single diagonal divides some nonzero entry. Hence every nontrivial exponent is \(O(n^2)\).

One can use the same row and column operations to solve (1), because unimodular integral changes of coordinates act by mutually inverse products of integer powers over any abelian group. Take unimodular \(U,V\) with \(UMV=D\), with positive nonzero diagonal entries \(s_1,\ldots,s_\rho\), and write the demand vector of (1) as \(b\). Apply \(U\) multiplicatively to \(b\) to get a vector \(a\). The diagonal equations are \(y_i^{s_i}=a_i\) for \(i\leq\rho\), and \(a_i=1\) for the zero rows. Each column past the diagonal allows a free nonzero scalar. Transform any solution \(y\) back by \(V\). Unit diagonals only assign a value, so the check requires at most the two claimed power equations.

## Finite-field decision, count, and witnesses

The tree pivots take polynomially many integral operations with small coefficients. Starting with the two nonzero residual rows, combine the first-row entries with two-column extended-gcd operations until only a gcd pivot remains. The first-row inputs and pivot are \(O(n)\), so this sweep uses \(O(n)\) transformations with entries of \(O(\log n)\) bits. Thus the second row has polynomial bit length. Repeat the sweep on the second row among columns with zero first entry. Its pivots are gcds of its input entries, so all of these column transformations and their accumulated product also have polynomial bit length. At most two columns remain. The rank-one case needs only a row gcd, and the full rank two-by-two case uses polynomial-time Smith reduction with unimodular multipliers. [Kannan and Bachem](https://doi.org/10.1137/0208040)

Write \(h=q-1\). In the cyclic group of order \(h\), the equation \(x^s=a\) is solvable precisely when \(a^{h/\gcd(s,h)}=1\), and then has \(\gcd(s,h)\) roots. No generator or discrete logarithm is needed for this test. Write \(m=|E(G)|\). If every row condition passes for \(\phi\), its exact transporter count is

\[
h^{m-\rho}\prod_{i=1}^{\rho}\gcd(s_i,h).
\]

Otherwise the count is zero. Sum over the candidates. The Smith multipliers have polynomial bit length, so powering in the finite field, transforming the demands and computing the counts all take polynomial bit time. To recover a scalar root when a test passes, take a linear factor of \(\gcd(X^{s_i}-a_i,X^q-X)\). Modular exponentiation computes the remainder of \(X^q-X\) without constructing a polynomial of degree \(q\). The gcd is squarefree and split. Standard randomized finite-field factorization gives the stated expected bound, since each \(s_i>1\) has degree \(O(n^2)\). Substitution in (1) checks a constructed transporter exactly. [Cantor and Zassenhaus](https://doi.org/10.1090/S0025-5718-1981-0606517-5)

## Sharpness and a separation example

The two possible nonunit Smith entries are both needed in general. Let \(P=\mathbb Z/a\times\mathbb Z/b\), with \(a,b\geq3\). Take two copies \(U,V\) of \(P\). The three neighbours in \(V\) of \(u_g\) have labels \(g+e_1,g+e_2,g\), in colours \(A,B,C\). The six ordered differences between the three shifts are distinct. A four-cycle would repeat an ordered difference, so there are no four-cycles. The shifts generate \(P\), giving connectivity. In the presentation, first eliminate \(v_g\) by the colour-\(C\) relation. The remaining relations are \(u_{g+e_1}=u_g+(t_A-t_C)\) and \(u_{g+e_2}=u_g+(t_B-t_C)\). They express every \(u_g\) in terms of \(u_0,t_A-t_C,t_B-t_C\) and impose precisely the torsion relations \(a(t_A-t_C)=0\) and \(b(t_B-t_C)=0\). Indeed, the formula \(u_{(i,j)}=u_0+i(t_A-t_C)+j(t_B-t_C)\) satisfies every relation modulo these two, yielding the inverse presentation. The cokernel is \(\mathbb Z^2\oplus\mathbb Z/a\oplus\mathbb Z/b\). Taking \(a=b=4\) gives two nonunit diagonals. Over \(\mathbb F_5\), even with all vertex demands equal to one and \(b_Ab_Bb_C=1\), either colour ratio \(b_A/b_C,b_B/b_C\) can be assigned independently, since cubing is a bijection on \(\mathbb F_5^\times\).

For a direct separation, take the bipartite graph with two copies of \(\mathbb Z/7\) and shifts \(0,1,3\), coloured by the shifts. Its six nonzero ordered differences are distinct, and it is connected. Over \(\mathbb F_5\), take all source weights equal to one and set the target weights to two at the two endpoints of a single edge, leaving all others equal to one. The map scaling only that edge coordinate by two gives a general-linear transporter. In any candidate special-linear transporter, multiplying all vertex equations in (1) forces the product of target weights divided by the product of source weights to be \((b_A b_B b_C)^2=1\), since every edge appears twice and each \(b_c=\sigma_c^{-1}\). The ratio in this example is four. The tensor pair thus has no special-linear transporter.

## Exact library interfaces and verification status

The intake contributes a concrete prime-field route for the only nonlinear witness tasks. `Hex.Berlekamp.berlekampFactor` in `HexBerlekamp.Factor` accepts a monic `FpPoly p` with `ZMod64.PrimeModulus p`. The root problem above supplies a squarefree monic polynomial after normalizing the gcd. `HexBerlekampTheory.irreducible_of_mem_berlekampFactor_of_gcd_eq_one` in `HexBerlekampTheory.Irreducibility` gives the irreducibility side under its positive-degree and prime-field premises. `Hex.FactoredPoly.ofFp` in `HexBerlekampTheory.FactorPoly` packages a checked coefficient identity and a checked irreducibility cover as a Mathlib factorization. A linear factor provides a root to check in (1). The word-size hypotheses and executable Berlekamp search confine this backend to supported prime fields. The finite-field theorem's general expected-time bound uses the independent factorization result cited above. [Computational split](https://github.com/leanprover/hex-berlekamp/blob/7c640a7fb32dd2eb7a319f7d204717af6a273a7a/HexBerlekamp/Factor.lean) · [Irreducibility theorem](https://github.com/leanprover/hex-berlekamp-theory/blob/7a85672cc6731649453c1e5a202dda9b7d7b6e2d/HexBerlekampTheory/Irreducibility.lean) · [Factorization certificate](https://github.com/leanprover/hex-berlekamp-theory/blob/7a85672cc6731649453c1e5a202dda9b7d7b6e2d/HexBerlekampTheory/FactorPoly.lean)

The proof is mathematical and informal. The Hex declarations above were retrieved by exact name from pinned sources. They supply an implementation interface for scalar witnesses and were neither imported into a Lean proof of this theorem nor invoked by the companion Python check. The companion independently enumerates chord scalars and compares its determinant counts with dense Smith predictions for small prime-field instances. It also compares the reduced matrix with the dense presentation and checks the stated separation and sharpness examples.
