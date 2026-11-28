# Undecidable extension between two fixed closed three-manifolds

**Theorem.** There exist a fixed closed orientable hyperbolic three-manifold \(M\), a fixed closed orientable Heisenberg nilmanifold \(Y\), and a fixed embedded bouquet \(A=S^1\vee S^1\subset M\) with the following property. Fix a loop \(z\) going once around the central circle fiber of \(Y\). Give the first circle of \(A\) the map \(z\) and the second circle the map \(z^e\), where \(e\in\mathbb N\) is the only input. Deciding whether that map extends continuously to \(M\) is computably enumerable complete under computable many-one reductions. Whenever an extension exists, every extension is surjective on fundamental groups.

The two marked loops are nullhomologous in \(M\), and the entire construction has torsion-free integral homology. Both manifolds are aspherical. The boundary maps on the two circles are fixed pointwise in the extension problem, using fixed based loop representatives and concatenation to represent powers. The Nil target can be chosen as the oriented circle bundle of Euler number one over the two-torus.

The fixed pair can in addition be chosen so that every input winding extends after replacing the target by the classifying space of any finite quotient of its fundamental group. These extensions admit a compatible choice across all finite quotients. They also extend to the coefficient targets over \(\mathbb Q\) and every \(\mathbb Z_p\), while existence over the original Nil target remains halting-complete.

**Boundary version.** There is a fixed compact orientable three-manifold \(N\) whose interior is a complete finite-volume hyperbolic manifold with two cusps. Extending a map from its entire torus boundary to the same fixed Nil three-manifold is halting-complete, when both meridians map constantly, the first longitude has fixed central winding one, and only the central winding of the second longitude varies. Every extension is surjective on fundamental groups, and the compatible finite-quotient extensions above continue to exist for every input.

There is also an all-ring realization theorem. For every finitely presented affine \(\mathbb Z\)-scheme \(X\), there exist a closed orientable hyperbolic three-manifold \(M_X\) with torsion-free homology and one embedded based circle \(A_X\) representing a commutator, such that the functor of relative homotopy classes into the Heisenberg classifying space \(BH(R)\) with boundary value \((0,0,1)\) admits the point functor \(X(R)\) as a natural retract. Over \(R=\mathbb Z\) the target is the same closed Nil three-manifold \(Y\). The maps realizing the retraction preserve points over nonreduced rings as well. The extra parameters have an explicit description as central coordinates, a matrix of determinant one, and the kernel of a linear system over the chosen point of \(X(R)\).

## Three-manifolds with prescribed triple products

Recall the realization theorem for the triple cup form of a closed orientable three-manifold. Given a finite-rank free abelian group \(V\) and an alternating \(\mathbb Z\)-trilinear form \(\mu\) on \(V\), one can obtain such a manifold with \(H^1(M;\mathbb Z)\cong V\), torsion-free homology and
\[
\langle x\smile y\smile w,[M]\rangle=\mu(x,y,w).
\tag{1}
\]
Here is a surgery construction that makes the free-homology assertion explicit. Choose a labeled basis of \(V\). Start with one \(S^1\times S^2\) summand per label, and one oriented \(T^3\) summand for each signed unit coefficient in the form on triples of distinct labels. The first summands furnish a basis in first homology with the desired labels. In each torus summand, impose the relation identifying each of its three axis classes with the corresponding original basis label. The signed units are implemented by the orientation of the torus summand. The relation classes are primitive and independent together, because each contains its own new axis with coefficient one and no other new axis.

Represent all relations by disjoint embedded oriented circles and perform integral Dehn surgery on those circles. General position for curves in dimension three gives the representatives. Each meridian vanishes in first homology of the link exterior: choose an integral 2-cycle in the original manifold with algebraic intersection one with that circle and zero with the others, using Poincaré duality and the primitive independent relation classes. Removing disks at intersections shows that the corresponding meridian combination bounds in the exterior. By the exact sequence of the original manifold and the exterior, the exterior therefore has the same first homology as the original manifold. Filling kills exactly the prescribed primitive relations, since the surgery slope is a longitude plus an integral multiple of the meridian. The resulting first homology is free on the original basis.

In the four-dimensional surgery trace its first homology is that same quotient, by the relative 2-handles. Consequently the outgoing first cohomology extends to the trace and restricts to the prescribed coordinate subspace of the incoming first cohomology. The two fundamental classes have the same image in the trace, with the boundary orientations accounted for. Evaluation of products of extended degree-one classes is therefore the same on the two ends. In the connected sum the only nonzero contributions are the torus forms, which restrict to the desired coefficients. This proves (1). Poincaré duality and the universal coefficient theorem give torsion-free homology in every degree. This construction is an instance of Sullivan’s realization of alternating cup forms. [Sullivan, *On the intersection ring of compact three manifolds*](https://www.math.stonybrook.edu/~dennis/publications/PDF/DS-pub-0019.pdf).

To make the source hyperbolic, use Ruberman’s theorem that a closed orientable three-manifold is integrally homology cobordant to a closed hyperbolic three-manifold. Both inclusions into the oriented cobordism induce isomorphisms on integral cohomology and carry the two fundamental classes to the same class with the appropriate orientations. Thus the new manifold has exactly the same labeled cup form (1) and free integral homology. The labels now specify cohomology classes and their dual homology basis on the hyperbolic manifold. The later construction only uses that information. [Ruberman, Theorem 2.6](https://msp.org/pjm/1990/145-1/pjm-v145-n1-p05-s.pdf).

## From coordinate equations to the cup form

For a unital commutative ring \(R\), write
\[
H(R)=R^3,\qquad (p,q,z)(p',q',z')=(p+p',q+q',z+z'+pq').
\tag{2}
\]
Its projection onto \(R^2\) is an extension by the central additive group \(R\). The multiplication law shows that the extension class is represented by the cup cocycle \((g,h)\mapsto p(g)q(h)\). Central commutators are given by
\[
[(p,q,z),(p',q',z')]=(0,0,pq'-p'q).
\tag{3}
\]

Take an integer arithmetic circuit for the equations of \(X\), with fresh output wires and with constants built from zero, one, addition and negation. Make basis labels \(a,b\) and two labels \(P_t,Q_t\) for each scalar wire \(t\). Let \(W\) be the free abelian group on this basis. Here and below a label also denotes its degree-one cohomology basis element. For each pair of distinct labels \(i,j\) the alternating form \(i^*\wedge j^*\) on \(W\) gives the two-by-two determinant of the pair of coordinate columns \((u_i,v_i),(u_j,v_j)\). On a normalized assignment require the columns on \(a,b\) to be \((1,0),(0,1)\). Then impose one alternating-form equation for each of the following tests, using \([i,j]\) in the table to denote that two-by-two determinant.

| Constraint | Alternating form evaluated on \((u,v)\) |
| --- | --- |
| Select the two cells of a wire | \([a,P_t]=0,\ [Q_t,b]=0,\ [P_t,b]-[a,Q_t]=0\) |
| Zero and one | \([P_t,b]=0\) or \([P_t,b]-[a,b]=0\) |
| Addition \(r=t+s\) | \([P_t,b]+[P_s,b]-[P_r,b]=0\) |
| Multiplication \(r=ts\) | \([P_t,Q_s]-[P_r,b]=0\) |

The selectors say precisely that the two wire columns are \((t,0)\) and \((0,t)\). This holds over every ring with no cancellation required. Negation is addition to zero. The product uses distinct labels even for a square. The equations thereby specify precisely the circuit solutions, with all auxiliary wire values determined by the inputs.

Call the resulting alternating forms \(\beta_1,\ldots,\beta_m\in\bigwedge^2 W^*\). Introduce one new cohomology label \(r_j\) per test and extend to the alternating 3-form
\[
\mu=\sum_{j=1}^m \beta_j\wedge r_j^*\qquad\text{on }V=W\oplus\bigoplus_{j=1}^m\mathbb Zr_j.
\tag{4}
\]
Take a hyperbolic \(M_X\) realizing this form. To test \(u\smile v=0\) in \(H^2(M_X;R)\), pair with every degree-one basis element and the oriented fundamental class. Poincaré duality, together with freeness of the integral homology, gives a perfect pairing over any \(R\). Formula (1) applies after coefficient change. Testing on \(r_j\) gives exactly \(\beta_j(u_W,v_W)=0\), independently of the coordinates on all \(r_i\). Testing on the original labels gives equations linear in the coordinates \((u_{r_j},v_{r_j})_j\), with coefficients determined by the original labels. They vanish simultaneously if these test coordinates are set to zero. Thus the normalized solutions to the cup equation project to \(X(R)\), and the projection has the section given by zero test coordinates and unique circuit values.

## Realizing the normalization with one commutator

Choose based loops \(g_i\) dual to the labeled basis of first cohomology. Represent \([g_a,g_b]\) by an embedded based circle. A piecewise linear graph in a three-manifold can be put in general position keeping a specified vertex, so a bouquet with any finite list of prescribed based classes can also be embedded. The marking is a subcomplex after triangulation. Prescribe the value \((0,0,1)\) in \(H(R)\) on this first marking.

For a homomorphism \(\pi_1(M_X)\to H(R)\), write \(u,v\in H^1(M_X;R)\) for its projected abelian characters. By (3) the marked commutator has the prescribed value exactly when the matrix with columns \((u_a,v_a),(u_b,v_b)\) has determinant one. Normalize by multiplying every column by its inverse. This preserves all pairwise determinants and the vanishing of \(u\smile v\). The latter follows from the alternating cup product in degree one on this module. Each integral degree-one basis class has square zero, since it is pulled back from a circle, and graded commutativity and coefficient change then give alternation for every \(R\), including characteristic two.

Conversely a cup-zero pair of characters admits a lift to (2), since the obstruction class is \(u\smile v\), and the hyperbolic source is aspherical. In group cochain terms a lift is a function \(z(g)\) with coboundary \(-u(g)v(h)\); a zero class gives such a function. Two lifts differ by a central character \(\pi_1(M_X)\to R_{\rm add}\). Since the \(g_i\) map to a basis of the free abelianization, there is a unique lift with specified central coordinates on those loops. In particular zero central coordinates determine a lift naturally in \(R\). This lift has the required value on the commutator because (3) depends solely on the two characters. The normalization, circuit reconstruction, zero test coordinates and zero central coordinates therefore give mutually compatible maps of functors
\[
X(R)\ \longrightarrow\ \operatorname{Hom}(\pi_1(M_X),H(R))_{[g_a,g_b]\mapsto(0,0,1)}\ \longrightarrow\ X(R),
\]
whose composite is the identity. The matrix before normalization is an arbitrary element of \(\mathrm{SL}_2(R)\). The test coordinates form the kernel of the homogeneous system just described. The central coordinates on the labeled basis are arbitrary. This proves the asserted fiber description. The middle functor is presented by polynomial equations from any finite group presentation, since multiplication and inversion in (2) are polynomial. The natural retraction also describes a retraction of the corresponding affine schemes.

For a connected CW pair with a fixed based map on its marking into an aspherical target, relative homotopy classes identify with group homomorphisms whose restriction is the specified based one. To see existence and uniqueness, lift the specified boundary map to the covering spaces with equivariance dictated by the homomorphism. Extend over relative cells using contractibility of the target universal cover, and use the same procedure on the homotopy cylinder. Alternatively, aspherical classification and homotopy extension first produce an extending representative, and the equivariant cylinder argument then supplies relative uniqueness. No injectivity of the marking on \(\pi_1\) is needed. The group \(H(\mathbb Z)\) acts freely as a lattice on the real Heisenberg group by left translations. The quotient is compact, because reducing its first two coordinates modulo one and then reducing the resulting central coordinate produces a compact fundamental region. The real group is homeomorphic to \(\mathbb R^3\). Its quotient is the required \(Y\). This completes the all-ring statement.

## A fixed hard instance with a single input winding

By DPRM choose one integer polynomial \(F(e,x_1,\ldots,x_s)\) for which \(F(e,x)=0\) has an integer solution in \(x\) exactly when machine \(e\) halts. Passage from natural witnesses to integer witnesses uses sums of four squares. Compile that one polynomial with \(e\) as an ordinary unpinned input wire. Use the fixed hyperbolic manifold for that circuit and mark the two commutators
\[
[g_a,g_b],\qquad [g_{P_e},g_b].
\]
Prescribe central values \((0,0,1)\) and \((0,0,e)\), respectively. Both elements of the source are nullhomologous. By (3), the first value provides the determinant-one normalization. After normalization, the second says exactly that the parameter wire has scalar value \(e\), since all determinants were unchanged. Existence of an extension is therefore equivalent to \(\exists x\in\mathbb Z^s\,F(e,x)=0\). The input boundary map is computably generated by repeating the same based loop, with the constant loop for exponent zero. Conversely, enumerate possible integer images of the generators of a fixed presentation of \(\pi_1(M)\) and evaluate its finitely many relators and the two markings using (2). This semidecides existence, proving completeness.

Every extending homomorphism projects onto \(\mathbb Z^2\), because the images of \(g_a,g_b\) give a unimodular pair. Their commutator is the generator of the central \(\mathbb Z\), and thus the homomorphism is onto \(H(\mathbb Z)\). This proves the extra surjectivity claim.

## Compatibility with every finite quotient

For the strengthened fixed template, replace the zero locus of \(F(e,x)\) by the affine system in additional coordinates \(t,u,b,w\)
\[
J=(u^2+2)\bigl(t^2 F(e,x)^2+(t-1)^2\bigr),\qquad
b^2=b,\quad bJ=0,\quad (1-b)(wJ-1)=0,\quad bw=0.
\]
This is the union of a closed branch and a principal open branch. Over \(\mathbb Z\) the open branch is impossible since \(u^2+2\) is never a unit. In the closed branch, the sum of squares forces \(t=1\) and \(F(e,x)=0\). Thus integral existence is unchanged. In the open branch set \(x=t=0\) and take \(u=0,w=1/2\) over \(\mathbb Z[1/2]\) or \(u=1,w=1/3\) over \(\mathbb Z[1/3]\), with \(b=0\) in both cases. These points are independent of \(e\) apart from its marked input coordinate. They give a rational point and points over every \(\mathbb Z_p\), using the first choice for odd primes and the second for \(p=2\). Taken together the latter are a point over \(\widehat{\mathbb Z}=\prod_p\mathbb Z_p\). This uses the coprime-denominator selector from the earlier probe work. [Bounded infinitesimal probes](https://github.com/Dugongue/MathProofs/blob/main/AffineSchemeCrossovers/ProbeIndistinguishability.md).

Use the natural section with zero auxiliary test and central coordinates to obtain one homomorphism \(\pi_1(M)\to H(\widehat{\mathbb Z})\) with the required two marked values. Reducing gives compatible homomorphisms to \(H(\mathbb Z/m\mathbb Z)\) for every \(m\). Every finite quotient of \(H(\mathbb Z)\) factors through one of these congruence quotients: if \(m\) is the exponent of the finite group, membership in the reduction kernel means all three coordinates are multiples of \(m\). In the normal form \((p,q,z)=(1,0,0)^p(0,1,0)^q(0,0,1)^{z-pq}\) all exponents are then multiples of \(m\), so the reduction kernel dies. Reduction maps give compatible homomorphisms to every finite quotient, independently of the chosen multiple of its exponent. The relative aspherical classification produces the stated extensions, with compatibility of relative classes. This proves the strengthening.

## Extension from the entire boundary of a two-cusped manifold

Represent the two marked commutators by disjoint oriented knots in their free homotopy classes, which is possible by general position in dimension three. By Myers’ excellent-link theorem they can be chosen in those same free homotopy classes so that the exterior \(N\) has complete finite-volume hyperbolic interior. The hypothesis in Myers’ Theorem 1.1 on sphere or projective-plane boundary components is vacuous for the closed ambient manifold. There are two boundary tori, corresponding to the two removed solid tori, and hence two cusps. [Myers, Theorem 1.1 and the discussion of hyperbolization](https://openresearch.okstate.edu/bitstreams/b948a900-c087-4041-a3c5-8ccea8ee57fe/download).

On each torus take a meridian and the longitude from a product identification of the solid torus with \(S^1\times D^2\). Prescribe the boundary map by composing the projection onto \(S^1\) with the corresponding central loop or its \(e\)-fold iterate. If the map extends over \(N\), glue the same projected maps on the solid tori to obtain a map on \(M\). The original two marked commutators then have the specified images, since those values are central and independent of a choice of paths from one basepoint. Conversely, if a map on \(M\) has these images on the commutators, its restrictions to the two solid tori are homotopic to the specified maps there. Each solid torus retracts onto its core and the two central images determine the required free homotopy classes of maps to the aspherical target. Homotopy extension for the union of the solid tori makes these agreements pointwise. The resulting map on \(N\) extends the entire prescribed boundary. This gives the same decision set. The inclusion of \(N\) in its meridional filling \(M\) is surjective on fundamental groups, so a map from \(N\) extending the specified boundary is surjective by applying the closed theorem to the filled extension. The same restriction and filling argument works for every finite coefficient target, and the compatible group homomorphisms for \(M\) restrict to compatible ones for \(N\).

## Scope and prior work

Earlier extension reductions already yield undecidability from finite complexes, and Diophantine interpretation in Heisenberg groups is classical. Recent work studies the equation problem for entire classes of Seifert three-manifold groups. Universality for three-manifold representation schemes is also known in germ form for complex representations. The statement here uses specifically the global extending classes of two fixed closed three-manifolds, a fixed two-circle marking and one variable central winding, with the additional global all-ring retract theorem. The simply connected closed manifold construction in the earlier affine work uses a different cup-degree shift. [Čadek, Krčál, Matoušek, Vokřínek and Wagner](https://arxiv.org/abs/1302.2370) · [Garreta, Miasnikov and Ovchinnikov](https://arxiv.org/abs/1805.04085) · [Gray and Levine](https://arxiv.org/abs/2512.07690) · [Kapovich and Millson](https://arxiv.org/abs/1303.2347) · [Earlier fixed aspherical target](https://github.com/Dugongue/MathProofs/blob/main/AffineSchemeCrossovers/ClosedAsphericalMappingSchemes.md).
