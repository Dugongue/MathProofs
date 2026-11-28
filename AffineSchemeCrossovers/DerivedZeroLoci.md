# Derived polynomial zero loci from relative topological mapping spaces

Let \(f=(f_1,\ldots,f_m)\) be polynomials in \(n\) variables over \(\mathbb Z\), specified by integer arithmetic circuits. In simplicial commutative rings write

\[
C_f=\mathbb Z[t_1,\ldots,t_n]\otimes^{\mathbf L}_{\mathbb Z[z_1,\ldots,z_m]}\mathbb Z,\qquad
z_j\longmapsto f_j,\quad z_j\longmapsto 0.
\]

This specifies the derived zero locus, including the derived data of the particular presentation. For every integer \(e\ge0\) choose an even \(d\ge e+2\). There is a polynomial-size, simply connected finite simplicial pair \((X_f,A_d)\) of dimension at most \(2d\), with the same boundary \(A_d=S^d\vee S^d\) for all \(f\), satisfying

\[
\operatorname{Map}_{\mathrm{sCAlg}_{\mathbb Z}}(C_f,R)
\ \simeq\
\tau_{\le e}\operatorname{Map}_{A_d}(X_f,Y_{R,d})
\tag{1}
\]

naturally in every \(e\)-truncated simplicial commutative ring \(R\). The target and marked boundary map depend only on \(R,d\). The statement concerns spaces of maps, preserving all homotopy groups in the displayed range, and applies to derived zero loci across all characteristics. In particular one can take \(d=2\) for ordinary rings, and \(d=4\) for \(e=1\) or \(2\).

## Coefficient spaces

Write \(\mathcal R=H(R_{\rm add})\) for the connective \(H\mathbb Z\)-module spectrum of the underlying simplicial abelian group, with its multiplication induced by \(R\). Write \(U(R)=\Omega^\infty\mathcal R\), its underlying space. Put

\[
B_{R,d}=(\Omega^\infty\Sigma^d\mathcal R)^2,\qquad
T_{R,d}=\Omega^\infty\Sigma^{2d}\mathcal R.
\]

The multiplication defines the cup-product map \(c:B_{R,d}\to T_{R,d}\). One model uses the smash of the two suspension spectra of the factors, followed by the two counits and multiplication on \(\mathcal R\). Set \(Y_{R,d}=\operatorname{hofib}(c)\). Ordinary rings give the ordinary cup-product target in the original realization. Choose the two integral anchor maps representing \((1,0),(0,1)\); their product in \(H^{2d}(A_d;\mathbb Z)\) is zero. Choose the boundary nullhomotopy over \(\mathbb Z\) once and use its image for every \(R\).

## Cell construction

The construction is the degree-\(d\) version of [universal relative mapping schemes](https://github.com/Dugongue/MathProofs/blob/main/Top10CrossoverProofs/UniversalRelativeMappingSchemes.md). Take a wedge of \(d\)-spheres with two anchor spheres \(a,b\) and one pair \(P_t,Q_t\) per wire. Attach \(2d\)-cells along the indicated mixed Whitehead brackets. The primary degrees \(x,y\) are pinned to \((1,0),(0,1)\) on \(a,b\). For distinct sphere labels \(D,E\) the entry of the cup product on the cell attached along \([D,E]\) is

\[
x_Dy_E+x_Ey_D.
\]

The product attaching map for \(S^d\times S^d\) gives this formula because \(d\) is even, and addition of attaching classes adds the mixed cup coefficients. The three equations attached by \([P_t,a],[Q_t,b],[P_t,b]-[a,Q_t]\) identify one common scalar \(t\) in the two wire copies and set their other two entries to zero. For multiplication, use \([P_t,Q_s]-[P_v,b]\) to impose \(ts=v\). Addition, negation, zero and one use tests with an anchor. The two copies of each wire keep the product coefficient equal to \(1\), also in characteristic two. Constrain the defining outputs to be zero. For fixed \(d\), each gate needs only a fixed finite collection of triangulated attaching-map templates. Simplicial mapping cylinders and cones as in the four-dimensional proof preserve the fixed boundary and give polynomial size in the circuit description. Binary constants are built by doubling and addition.

## Relative cochains and the cup map on derived points

Use the based mapping space with a fixed restriction on \(A_d\), or equivalently its homotopy-fiber model. Write \(r\) for the number of non-anchor \(d\)-spheres and \(s\) for the number of \(2d\)-cells. The reduced integral chain object of \(X_f/A_d\) is \(\mathbb Z[d]^r\oplus\mathbb Z[2d]^s\) in the derived category. This can be seen directly by choosing cycles for the two cellular bases, with the anchor representatives chosen compatibly in the absolute chain object. The statement follows since the cellular cochain differential vanishes.

Maps to \(\Omega^\infty\Sigma^j\mathcal R\) are computed by applying the \(H\mathbb Z\)-module function spectrum to \(H\mathbb Z\wedge\Sigma^\infty(X_f/A_d)\). When the boundary map is fixed and nonzero, choose a fixed integral extension of it in the corresponding Eilenberg–Mac Lane space and translate by its image. For the primary maps such an extension exists since restriction on \(H^d\) is onto, and one can choose it with all non-anchor primary coordinates zero. In the target of the cup map choose a null extension of the prescribed boundary cup value and chosen nullhomotopy. This exists by homotopy extension starting at the zero map on \(X_f\) and extending the boundary nullhomotopy in reverse. The choices are made integrally and transported along \(\mathbb Z\to R\).

Consequently the space of primary relative maps is equivalent to

\[
U(R)^{2r}\times (\Omega^\infty\Sigma^{-d}\mathcal R)^{2s}.
\]

If \(R\) is \(e\)-truncated and \(d>e\), the second factor is contractible. The relative space receiving the cup map is

\[
(\Omega^\infty\Sigma^d\mathcal R)^r\times U(R)^s.
\]

The top-cell projection of the cup map is the polynomial operation given by the cells. To justify this at the level of spaces, for *all* simplicial \(R\) include \(U(R)^{2r}\) by setting its primary top-cell coordinates to zero. Compose with the full cup map and the top-cell projection. This is a natural transformation from \(U(-)^{2r}\) to \(U(-)^s\). These functors are corepresented in simplicial commutative rings by the discrete polynomial rings in \(2r\) and \(s\) variables, respectively. By Yoneda the transformation is determined by its value on the universal tuple in the ordinary polynomial ring. There the mixed cup calculation above determines exactly one ordinary polynomial per output. Thus the operation on derived test rings is the indicated polynomial map up to natural equivalence. Restriction to the truncated test rings recovers the full primary space because the discarded primary factor is contractible. [Polynomial rings as free objects in simplicial commutative rings](https://people.math.harvard.edu/~lurie/papers/DAG.pdf).

Taking a homotopy fiber over zero in the top-cell coordinates now gives the derived zero equations of the circuit. More precisely, projection from the relative maps into \(Y_{R,d}\) to this homotopy fiber has fibers equivalent to

\[
(\Omega(\Omega^\infty\Sigma^d\mathcal R))^r.
\]

This follows from the description as a primary map with a nullhomotopy of its cup product extending the given boundary nullhomotopy. The omitted bottom-cell cup coordinates take values in a \((d-1)\)-connected space, so their nullhomotopy space is \((d-2)\)-connected. When \(d\ge e+2\), this projection is therefore an equivalence after \(\tau_{\le e}\).

## Derived elimination of the circuit variables

The wire equations first eliminate the two zero coordinates and identify the two copies of each scalar by an invertible linear change. The gate equations then eliminate fresh output variables in circuit order. This last statement holds for derived zero loci as follows. If some equations are \(u=0\) and the remaining outputs are \(g(v,u)\), express \(g(v,u)-g(v,0)\) as a polynomial linear combination of the coordinates \(u\). A fiberwise triangular automorphism of the trivial output bundle sends \((u,g(v,u))\) to \((u,g(v,0))\) and preserves the zero section. It induces an equivalence on derived fibers. The constraint \(u=0\) on its own coordinate space has contractible fiber. For a monic gate \(w-a(v)=0\), the source change \(u=w-a(v)\) gives this situation. Repetition leaves precisely the derived zero locus of \(f\), whose points are the homotopy fiber of \(f:U(R)^n\to U(R)^m\) by the homotopy pushout defining \(C_f\). This fiber is \(e\)-truncated because both its input and output are. Equation (1) follows.

For arbitrary connective \(R\), apply (1) to the coefficient rings \(\tau_{\le e}R\) and take the inverse limit of the resulting \(e\)-truncated models. The transition maps can be taken from the top-cell polynomial fibers in the proof. This recovers \(\operatorname{Map}(C_f,R)\) since \(R\simeq\lim_e\tau_{\le e}R\) and mapping out of a fixed object preserves limits.

## Corollary for arbitrary coefficient rings in fixed dimension

For every \(f\), there is a finite mapping diagram whose source complexes have dimension at most five and whose homotopy fiber recovers \(\operatorname{Map}(C_f,R)\) naturally for every simplicial commutative ring \(R\). Its defining map extends prescribed bottom-sphere maps, takes their cup product, and evaluates it on suspended top-cell spheres. This result uses the projected cup map in the diagram. Equation (1) describes the single relative mapping space after truncation.

Take \(d=2\) and let \(W\subset X_f\) be the wedge of bottom spheres, including the two anchors. Let \(P\) be the product of those spheres. The map \(W\to P\) that includes each sphere as its own factor kills every attaching map. In fact, each bracket term uses two distinct factors, and its projection to each factor is null because one bracket input projects to zero. Choose the resulting extensions over the top cells to obtain a map \(X_f\to P\) extending the inclusion of the wedge. Its components are fixed maps \(p_i:X_f\to S_i^2\) to the individual bottom spheres. Given bottom maps \(b_i:S_i^2\to B_{R,2}\), with the prescribed anchor maps on the two anchors, extend by taking the sum of the maps \(b_i\circ p_i\). This extension is natural in \(R\) and in the bottom data. The bottom data space is \(\operatorname{Map}_{A_2}(W,B_{R,2})\simeq U(R)^{2r}\). The product \(P\) is used to construct the maps \(p_i\) and does not occur as a source in the mapping diagram.

There is a based map \(\Sigma P\to\Sigma W\) obtained by pinching \(\Sigma P\) into a wedge of copies of itself and suspending the projection to the corresponding factor on each copy. Its composite with \(\Sigma W\to\Sigma P\) is homotopic to the identity on each suspended sphere and hence on the wedge. This proves that suspension kills the attaching maps, since the maps were killed after passage to \(P\). In particular the suspended attachments in \(\Sigma(X_f/A_2)\) are null. Choose one oriented map \(S^5\to\Sigma(X_f/A_2)\) for each top cell by using a nullhomotopy of its suspended attaching map. They represent the individual suspended top-cell homology generators.

Take the cup product of the primary extension on \(X_f\), translate by the integral null extension of the boundary cup value from above, and pass to the quotient \(X_f/A_2\). A based map from this quotient to \(T_{R,2}\) adjoints, using \(T_{R,2}\simeq\Omega(\Omega^\infty\Sigma^5\mathcal R)\), to a map from the suspended quotient to \(\Omega^\infty\Sigma^5\mathcal R\). Restrict along the selected \(5\)-spheres. The resulting map \(U(R)^{2r}\to U(R)^s\) is natural. At the universal discrete polynomial ring it reads off the same oriented top-cell cup coefficients as above. The integral translation contributes zero to those coefficients because it is nullhomotopic on \(X_f\). Polynomial corepresentability therefore identifies this map with the circuit equations for every \(R\), and derived elimination identifies its homotopy fiber over zero with \(\operatorname{Map}(C_f,R)\).

## Scope

The earlier Whitehead-product construction supplies polynomial encodings into the existence of extensions, and the four-dimensional scheme theorem supplies the ordinary point functor. Here the extra ingredients are free-polynomial representability for the derived cup operation, a connectivity estimate that removes the redundant nullhomotopies, and derived elimination of the gate variables. The restriction to a polynomial derived zero locus is part of the claim. [Čadek–Krčál–Matoušek–Vokřínek–Wagner](https://arxiv.org/abs/1302.2370).
