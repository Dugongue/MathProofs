# Relative mapping presentations of quasi-projective schemes

Let \(Y_R\) be the coefficient target in [universal relative mapping schemes](https://github.com/Dugongue/MathProofs/blob/main/Top10CrossoverProofs/UniversalRelativeMappingSchemes.md), the homotopy fiber of the universal cup product \(K(R,2)^2\to K(R,4)\). A relative mapping class fixes prescribed maps on a common anchor subcomplex. The affine construction associates to any finite polynomial system over \(\mathbb Z\) a relative 4-complex whose relative \(Y_R\)-mapping classes identify naturally with solutions over every commutative ring \(R\). We use its gate construction, in which an input variable is the degree of a named 2-cell, auxiliary variables are uniquely determined by the inputs, and copies of circuits can share literal input 2-cells and the anchors. All 2- and 4-cells in a chosen circuit can be labeled and oriented, and gluing takes place along the inputs and anchors.

## Theorem

For every quasi-projective scheme \(X\) of finite presentation over \(\mathbb Z\), there is a cosemisimplicial family of finite anchored 4-complexes \(K_n(X)\), \(n\geq 0\), along order-preserving injections, with natural weak equivalences

\[
\left\|[K_\bullet(X),Y_R]_{\rm rel}\right\|\simeq X(R)_{\rm disc}
\]

for all commutative rings \(R\). For fixed \(X\), \(K_n(X)\) has \(O((n+1)^2)\) cells. The construction includes projective points over \(R\) whose homogeneous line is a nontrivial projective \(R\)-module. Every morphism \(f:X\to Z\) of such schemes is induced by a span of anchored semisimplicial mapping presentations whose left leg becomes a weak equivalence after realization. Composite morphisms admit a common span refinement inducing their composite.

## An affine atlas that lifts points over every ring

Embed \(X\) as an open subscheme of its scheme-theoretic closure \(\bar X\subseteq \mathbb P^{N-1}_{\mathbb Z}\). Choose finitely many homogeneous polynomials \(f_j\) defining \(\bar X\) and finitely many homogeneous \(g_l\) with \(X=\bar X\cap\bigcup_lD_+(g_l)\). This is possible because the projective space and its homogeneous coordinate ring are Noetherian. We use the lines convention for projective space. An \(R\)-point of projective space is a rank-one locally free submodule \(L\subseteq R^N\) with locally free quotient. That quotient is a finitely generated projective \(R\)-module, so the inclusion \(L\subseteq R^N\) splits over \(R\).

Define the affine scheme \(P_X\) by the following equations for an \(N\times N\) matrix \(E\) and scalar witnesses \(w_{li}\), where \(v_i=E_{\cdot i}\).

\[
E^2=E,\qquad \hbox{all two-by-two minors of }E=0,\qquad
\operatorname{tr}(E)=1,\qquad f_j(v_i)=0\quad(\hbox{all }j,i),\qquad
\sum_{l,i}w_{li}g_l(v_i)=1.
\]

An idempotent splits the ambient free module as image plus kernel. At every prime, the two summands become free after localization, and the matrix is conjugate to a diagonal projection. The minors force rank at most one over the residue field, and the trace forces rank one. Thus \(L=\operatorname{im}(E)\) is the line required for a projective point. Conversely a projection onto any such line satisfies the matrix equations.

Locally trivialize \(L\) by a vector \(v\) and write \(v_i=a_i v\). The columns generate \(L\), so the \(a_i\) generate the unit ideal. For a homogeneous \(f\) of degree \(d\), \(f(v_i)=a_i^d f(v)\). The \(a_i^d\) generate the unit ideal, which proves the asserted equivalence with \(f(v)=0\) over rings with nilpotents as well. The degree-zero case uses the same formula with \(a_i^0=1\). For the open condition, at each prime at least one column generates the residue-field line. The ideal of all \(g_l(v_i)\) is therefore the unit ideal precisely when the projective point lands in the chosen open. In that case the defining equation for \(w\) can be solved over \(R\). This constructs a morphism \(q_X:P_X\to X\) whose map on \(R\)-points is surjective for every \(R\).

For \(p,p'\in P_X(R)\) with idempotents \(E,E'\), equality of their images is equivalent to the following equations.

\[
q_X(p)=q_X(p')\quad\Longleftrightarrow\quad EE'=E'\ \text{ and }\ E'E=E.
\]

Indeed, \(E\) acts as the identity on its image and the two equations express both inclusions of image submodules. The weights \(w\) impose no further equality conditions.

## Topological construction and descent

Use a fixed polynomial circuit for \(P_X\) and a fixed circuit for the displayed test on two copies of its inputs. For \(K_n(X)\), attach the \(n+1\) copies of the first circuit to the same anchors, and attach a copy of the second circuit for each ordered index pair \(i<j\), sharing the appropriate input cells with the \(i\)-th and \(j\)-th vertex circuits. Use fresh auxiliary cells for each circuit. An order-preserving injection sends every labeled circuit to the one labeled by the image index or pair, with the same attachment maps. Thus it gives a cellular map of pairs, and these maps compose exactly. Each relative mapping-class functor is contravariant in the source, so the mapping classes form a semisimplicial set. The affine relative realization identifies it degree-by-degree with

\[
P_X(R)^{\times_{X(R)}(n+1)}.
\]

This agrees with the face maps because those maps restrict the same degree coordinates. The number of copies is \(n+1+\binom{n+1}{2}\), giving the size bound. The augmentation to \(X(R)\) decomposes the thick realization into the thick realizations of \(T^{n+1}\) for the fibers \(T=q_X^{-1}(x)(R)\). Each \(T\) is nonempty. Choose \(t\in T\) for the verification and prepend \(t\) to every tuple. Given a simplex with barycentric coordinates \((u_0,\ldots,u_n)\), assign the enlarged simplex coordinates \((1-s,su_0,\ldots,su_n)\) as \(s\) ranges from \(0\) to \(1\). This respects face identifications and contracts the fiber to \(t\). The augmentation is itself canonical, which gives its naturality in \(R\). For an empty \(X(R)\), all terms of the augmented family are empty.

## Maps and composition

For \(f:X\to Z\), let \(P_f\subseteq P_X\times P_Z\) be the pullback of the graph of \(f\) by \(q_X\times q_Z\). The graph is closed since \(Z\) is separated over \(\mathbb Z\). Thus \(P_f\) is affine of finite presentation. Its polynomial presentation includes the chosen equations and coordinate variables of \(P_X\) and \(P_Z\). Define a relative 4-complex with \(P_f\)-circuits at each vertex and the equal-image equations for both \(X\)- and \(Z\)-coordinates at each pair. Both previous labeled constructions embed into this construction via the vertex and pair subcircuits. Restrictions give maps from the realized \(P_f\)-presentation to both realized presentations. The map \(P_f(R)\to X(R)\) is surjective since every \(x\) and \(f(x)\) have lifts, and a pair of vertices agrees over \(X(R)\) precisely when the pair satisfies the source and target equality tests. The same contraction therefore identifies the left leg with a weak equivalence and the right leg with \(f(R)\).

For \(X\xrightarrow f Z\xrightarrow g W\), use \(P_f\times_{P_Z}P_g\) as vertex scheme with all three sets of pair tests. Its \(R\)-points again lift every \(x\in X(R)\). Include the chosen graph subcircuits for \(P_f,P_g,P_{g\circ f}\) in each vertex, sharing the already identified atlas inputs, and include each adjacent pair of equality-test circuits in the new pair tests. The equations for \(P_{g\circ f}\) already hold on the fiber product, so adding their copies with fresh auxiliary wires leaves the solution functor unchanged. Restriction gives face-compatible refinements of all three spans, and the augmentations identify the resulting composite map with \((g\circ f)(R)\). All constructions are natural in the coefficient ring.

## Scope and prior work

The affine atlas uses the classical splitting of projective modules and is closely related to Jouanolou devices for projective space. Čech realization of a surjection on points is also standard. The theorem adds their explicit realization by a single fixed two-stage coefficient target and finite 4-complexes whose face maps agree on the complexes themselves. The case of the Jouanolou device over the projective line is discussed by [Balch Barth, Hornslien, Quick, and Wilson](https://arxiv.org/abs/2306.00628).
