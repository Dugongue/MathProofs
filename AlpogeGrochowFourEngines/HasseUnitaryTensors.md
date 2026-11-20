# Quadratic norm descent for unitary tensor systems

Let $F$ be a number field and let $K/F$ be a quadratic étale algebra with its nontrivial involution. It can be a quadratic field or $F\times F$ with the factors exchanged. Let $A$ and $A'$ be finite étale $F$-algebras. Put $L=A\otimes_F K$ and $L'=A'\otimes_F K$, with involution induced by that of $K$. Denote the relative norm $u\mapsto u\bar u$ by $N$. The data below comprise explicit forms and order-three tensor records over $K$.

For each mode $i\in\{1,\ldots,s\}$ there is a copy of $L$ with the nonsingular $K/F$-Hermitian form
$$
h_i(x,y)=\operatorname{Tr}_{L/K}(b_i x\bar y), \qquad b_i\in A^\times.
$$
The target has coefficients $b'_i\in (A')^\times$. For each record $\ell$ choose an ordered triple $(i_{\ell,1},i_{\ell,2},i_{\ell,3})$ of modes. Repeated modes are permitted, with one common transporter for all their occurrences. The record is
$$
T_\ell(x_1,x_2,x_3)=\operatorname{Tr}_{L/K}(t_\ell x_1 x_2 x_3),\qquad t_\ell\in L^\times,
$$
and similarly $T'_\ell$ with $t'_\ell\in (L')^\times$. Each mode occurs in some record, and the incidence hypergraph is connected. Let $M_{\ell i}$ be the number of occurrences of mode $i$ in record $\ell$. Assume each nonzero Smith invariant of the integer matrix $M$ equals one. A single three-mode multiplication record satisfies this hypothesis. It also holds for totally unimodular incidence matrices. Invertibility of the $t_\ell$ is used so that each record sees every étale field component.

**Theorem.** Unitary isomorphism of the two tensor systems is exactly a perfect matching problem between the rational field factors of $A$ and $A'$. A candidate factor isomorphism is a valid edge precisely when its tensor constants satisfy the multiplicative row dependencies of $M$, its norms satisfy the row compatibility equations, and its individual norm requests satisfy a finite list of quadratic local norm tests. For a specified étale identification, the unitary system has a global transporter if and only if it has compatible transporters over all completions inducing that identification. The algorithm can test different isomorphisms on different matched field factors. The rank-one norm constraints can be solved independently after integer elimination, even though the original tensor equations use a common transporter. No analytic RH or GRH hypothesis is used.

The arithmetic engine is the quadratic local-to-global norm result implemented as **GlobalTheory.QNorm.hasseNormSt** in the Alpöge release. The argument below turns a linked unitary transporter system into equations to which that theorem applies. The nondegenerate trace pairings also use the separable trace construction underlying **GlobalTheory.CompanionTheory.SW.CoordMat.traceGram_det_ne_zero**. [Alpöge's announcement](https://alpo.ge/remark.pdf) · [Release import bridge listing the quadratic norm proof](https://raw.githubusercontent.com/CocoSgt/riemann-hypothesis-lean/main/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean)

## 1. The tensors force an étale algebra witness

Use the convention
$$
T'_\ell(g_{i_{\ell,1}}x_1,g_{i_{\ell,2}}x_2,g_{i_{\ell,3}}x_3)=T_\ell(x_1,x_2,x_3).
$$
For a single record the centroid action consists precisely of triples of multiplications by a common element of $L$. To prove this, let $C_1,C_2,C_3$ be a centroid triple. Moving $C_1$ from the first slot to the second and varying the third variable gives $(C_1x)y=x(C_2y)$, since $t_\ell$ is a unit and the trace pairing of an étale algebra is perfect. Substituting $x=1$ and $y=1$ shows that both operators are multiplication by $C_1(1)=C_2(1)$. Comparing with the third slot gives the same answer there. This reasoning also applies when a mode repeats: the tensor records define independent input arguments in their slots, while the isomorphism uses the same linear map on repeated slots.

Any transporter conjugates these centroids, so for each record it induces a $K$-algebra isomorphism $L\to L'$. Two records with a common mode induce the same isomorphism because conjugation of the faithful scalar action on that mode determines it. Connectedness yields a single isomorphism $\sigma$ for all records. In every mode
$$
g_i(x)=u_i\sigma(x),\qquad u_i=g_i(1)\in(L')^\times.
$$
Indeed $g_i(a x)=\sigma(a)g_i(x)$ and invertibility forces multiplication by $u_i$ to be invertible.

The adjoint of multiplication by $a$ for $h_i$ is multiplication by $\bar a$, as seen in the trace formula. A Hermitian isometry preserves this adjoint operation, so $\sigma(\bar a)=\overline{\sigma(a)}$. Thus $\sigma$ restricts to an $F$-algebra isomorphism $A\to A'$ between fixed algebras. Conversely every such $\sigma$ extends uniquely by the identity on $K$. This follows from the explicit tensor-product presentation of $L,L'$, including the split quadratic case. The same reconstruction is valid after completing $F$.

## 2. Exact multiplicative equations on one edge

Fix a candidate $\sigma$ and work componentwise on $A'$. In a target field factor $B$ let $C=B\otimes_F K$, a quadratic étale algebra over $B$. All expressions below are projected to that component. Write
$$
a_i=\frac{\sigma(b_i)}{b'_i}\in B^\times,\qquad z_\ell=\frac{\sigma(t_\ell)}{t'_\ell}\in C^\times.
$$
The tensor and form equations are exactly
$$
N(u_i)=a_i,\qquad \prod_i u_i^{M_{\ell i}}=z_\ell.
$$
For the tensor equation, use that $\sigma$ respects the trace and vary the product of arguments over all of $L$. For the Hermitian equation, the same argument with $x\bar y$ gives $b'_iN(u_i)=\sigma(b_i)$. Conversely these identities give each original equation in the supplied forms, so the numerical norm witnesses produce actual linear transporters.

Let $P M Q=\operatorname{diag}(I_r,0)$ be Smith reduction by integer unimodular row and column matrices, with $r$ the rank. Set $u_i=\prod_j w_j^{Q_{ij}}$ and $\widetilde z_\ell=\prod_j z_j^{P_{\ell j}}$. Since the changes are group automorphisms on products of $C^\times$, the tensor equations say exactly
$$
w_j=\widetilde z_j\ (j\le r),\qquad \widetilde z_\ell=1\ (\ell>r).
$$
The required norms of the $w_j$ are $\widetilde a_j=\prod_i a_i^{(Q^{-1})_{ji}}$. This proves the following equivalent tests without quantifying over tensor maps.

1. The multiplicative dependencies $\widetilde z_\ell=1$ hold whenever $\ell>r$.
2. $N(z_\ell)=\prod_i a_i^{M_{\ell i}}$ for every row $\ell$.
3. Every $a_i$ is in $N(C^\times)$.

Necessity is immediate from the equations. For sufficiency, choose the fixed $w_j=\widetilde z_j$. Item 2, after the row operations, gives $N(w_j)=\widetilde a_j$ for each fixed coordinate. For each free coordinate $\widetilde a_j$ is a product of powers of elements in the norm image by item 3, so it has a preimage $w_j$. These choices are independent. Returning by the column transformation produces all original $u_i$ on that factor. The proof also shows the precise structure when $r=s$: the fixed coordinates alone determine all scale factors.

For a single cubic record the formula is particularly simple. The product $a_1a_2a_3$ must equal $N(z_1)$. Choose preimages of $a_1,a_2$ and put $u_3=z_1(u_1u_2)^{-1}$. Its norm is automatically $a_3$. Thus only two independent norm searches are needed and the solution set for a fixed edge, when nonempty, is a torsor for two copies of the norm-one group of $C/B$.

## 3. Finite local tests and global matching

For a split quadratic algebra $C/B$, its norm map is just multiplication of two coordinates and is surjective. For a field, write $C=B(\sqrt{\delta})$. The equation $N(x+y\sqrt\delta)=a$ is the quadratic norm-form equation $x^2-\delta y^2=a$. The released theorem **hasseNormSt** gives a global solution from the real and finite local solutions. At complex places the quadratic algebra splits. At split finite places the norm is onto, and at an unramified nonsplit finite place a unit is a norm. Consequently it suffices, for item 3, to check real places and finite places dividing the relative discriminant or a numerator or denominator ideal of one of the requested $a_i$. Equivalently one can test the local Hilbert symbols $(\delta,a_i)_v$. Conditions 1 and 2 are global identities of explicit constants. An incorrectly calibrated row is already detected by any completion because a number field embeds into each completion. This proves the fixed-identification local-to-global statement. [Quadratic norm residue criterion](https://kskedlaya.org/cft/sec_localrecip.html)

For unlabelled global input, use the primitive field factors of $A$ and $A'$ as vertices of a bipartite graph. Between two vertices, test each $F$-field isomorphism. For a successful one, keep the edge with that isomorphism as its label. This is finite, since the number of isomorphisms of a candidate pair is at most the field degree. An actual global tensor transporter supplies a perfect matching of these factors and validates its edges. Conversely choose one successful isomorphism per edge of a perfect matching. Their product is the required global $\sigma$, and the constructed block scale factors combine into units of $L'$. The tensor trace decomposes as a sum across the factors, so this independent assembly gives the original unitary system isomorphism.

This is an exact matching reduction with a polynomial number of arithmetic tests. For the single-record case and for totally unimodular incidence matrices, the multiplicative dependencies can be checked without large exponents. For the latter choose an invertible rank-$r$ minor. Its determinant is $\pm1$, and Cramer's rule and total unimodularity give coefficients in $\{0,\pm1\}$ for solving the pivot block and expressing dependent rows. The equations then involve only products of polynomially many input factors. The arithmetic recurrence for a general primitive matrix can be kept in power-product form. The statement does not require a deterministic polynomial-time factoring algorithm for integers or number-field ideals. The split or local norm checks can be run with explicit prime-ideal support data, and no enumeration of all global unit solutions is necessary.

For clarity about the role of matching, local transporters selected at different places can have different actions on the étale factors. The theorem evaluates the finite-place norm conditions along one candidate global matching at a time. It therefore applies to fixed centroid matching as a local-to-global theorem and to arbitrary global factor permutations as a perfect-matching classification.

## 4. An unmarked local-to-global theorem

The preceding matching condition becomes automatic on a directly testable class, without supplying any étale identification. For each row define the element
$$
q_\ell=\frac{N(t_\ell)}{\prod_i b_i^{M_{\ell i}}}\in A^\times .
$$
For each integral row dependency $\lambda$ with $\lambda^{\mathsf T}M=0$, define the element
$$
r_\lambda=\prod_\ell t_\ell^{\lambda_\ell}\in L^\times .
$$
A basis of the integer relation lattice suffices. Choose one fixed $F$-basis of $K$ and take both $A$-coordinates of each $r_\lambda$ in that basis. Require that these coordinates together with the $q_\ell$ generate $A$ as an $F$-algebra, and impose the analogous condition on the target. An isomorphism carries each displayed invariant to its corresponding target invariant. For $q_\ell$ this follows by taking the norm of the row equation and using the form equations. For $r_\lambda$ all the transporter scale factors cancel by the row dependency. Extracting its coordinates commutes with the isomorphism because it fixes $K$.

**Corollary.** Under this generation condition, the unmarked tensor systems are globally unitarily isomorphic if and only if they are unitarily isomorphic over every completion of $F$.

To prove this, list the generating invariants in a fixed order as $\xi_1,\ldots,\xi_b$ and $\xi'_1,\ldots,\xi'_b$. A local isomorphism of the unmarked data induces an $F_v$-algebra isomorphism of the base-changed fixed algebras carrying every $\xi_j$ to $\xi'_j$, by Section 1. The two polynomial evaluation maps $F[X_1,\ldots,X_b]\to A,A'$ have identical kernels. Indeed any relation on one side also holds on the other side after extending to a single completion with a local isomorphism, and a finite-dimensional $F$-vector space embeds in its completed scalar extension. Since both evaluations are surjective, equality of kernels defines a unique global $F$-algebra isomorphism $\sigma:A\to A'$ with those invariant correspondences. Every local induced isomorphism equals its base change since the invariants also generate after base change. The fixed-identification result now supplies the global transporter.

The generation test uses iterated multiplication and linear span in the multiplication table, stopping once the span stabilizes or has dimension $\dim_F A$. For one cubic record it needs only the element $q_1$. For instance, in a split algebra $F^k$ pairwise distinct coordinates of $q_1$ suffice by Lagrange interpolation. In a field factor an ordinary primitive element suffices. This case allows arbitrary sizes and uses local transporters without supplying their actions on the field factors.

## 5. Explicit example

Take $F=\mathbb Q$, $K=\mathbb Q(i)$, one factor $A=F$, and a single cubic tensor. Use source weight $t_1=5$ and target weight $t'_1=1$. Take all $b'_i=1$ and $(b_1,b_2,b_3)=(5,5,1)$. Then $N(z_1)=25=a_1a_2a_3$, and the exact unitary transporter is
$$
u_1=2+i,\qquad u_2=2-i,\qquad u_3=1.
$$
This example has coupled tensor scaling, even though its three unitary norm checks are separate. The same construction assembles across any number of repeated rational factor types using the matching graph.

The transporter classification and reduction are proofs in prose. The accompanying Lean lemma checks the multiplicative gluing step for a single triple under an arbitrary group norm homomorphism.

## 6. Recover the diagonal data from raw arrays

The centroid proof also permits the family to be used without supplying matched étale field factors. For raw tensor records promised to have the stated form, solve the linear centroid equations treating the three arguments as separate slots. Project a record's centroid to the endomorphisms of each of its modes. These maps are algebra isomorphisms on the stated family by Section 1, so a shared mode identifies the corresponding projected actions of different records. Starting with a root record, propagate these identifications along the connected incidence graph. They agree around every cycle for a tensor of the stated form.

The resulting algebra action on every mode is free of rank one over $L$. After étale factoring, a vector whose projection to every simple component is nonzero gives a module basis; obtain one by summing a chosen nonzero vector from each factor. The Hermitian adjoint recovers the involution on the centroid by linear equations. The fixed algebra is $A$. In the selected module coordinates, nondegeneracy of the trace pairing determines $b_i$ from $x\mapsto h_i(x,1)$ and $t_\ell$ from $x\mapsto T_\ell(x,1,1)$. Here the $1$ in a slot denotes its chosen module frame vector. These are linear solves over $K$. Check the full identities and the unit requirements in the supplied arrays. Cohomology or transporter search is unnecessary for these steps. A raw recognition algorithm can reject if the indicated product actions, involution, cycle consistencies, ranks or exact tensor identities fail. Over a split $K$ each field-algebra operation is performed on its two components. Thus the arithmetic factor matching and local norm predicates operate on recovered data as well as on explicitly presented models.
