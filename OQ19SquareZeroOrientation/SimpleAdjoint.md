# A multiplicity-space reduction for square-zero orientation

Work over \(F=\mathbb F_3\). In the square-zero normal form, take the Lagrangian quotient \(U\), of odd dimension \(m\), and its based space of alternating forms \(J\subseteq\bigwedge^2_F U^*\). The descended forms have zero common radical. Write \(\beta:\bigwedge^2_F U\twoheadrightarrow J^*\) for their simultaneous evaluation. An ordinary congruence \(p:U\to U'\) transports \(J\) by the restriction of \(\bigwedge^2 p^{-\mathsf T}\). The prescribed sign is the determinant of this restriction. A quotient congruence lifts to an anchor-preserving congruence of the full square-zero pencils by \(p\oplus p^{-\mathsf T}\) in symplectic frames. We therefore work on \(U,J\).

## Theorem

Suppose the projected adjoint algebra of \(\beta\) is simple. Its matrix algebra presentation is \(M_d(E)\), where \(E=\mathbb F_{3^e}\). Put \(r=m/(ed)\). There is a deterministic polynomial-time reduction of the prescribed sign test to the following problem.

- On each side construct an \(r\)-dimensional \(E\)-space \(R\) and an explicitly based \(F\)-linear subspace \(K\subseteq\bigwedge^2_E R\). The subspace need not be \(E\)-linear.
- Ask for a semilinear isomorphism \(H:R\to R'\), with field automorphism \(\sigma\in\operatorname{Gal}(E/F)\), for which \(\bigwedge^2_E H\) carries \(K\) onto \(K'\) with a specified \(F\)-determinant on \(K\).

The new label dimension can be made at most \(\min\{\dim_F J, e\binom r2-\dim_F J\}\). If \(E=F\), the output is a same-field alternating-space sign test on an ambient space of dimension at most \(m/d\), including for unrestricted label dimension. The subspace, its bases and the sign calibration are computed before any isomorphism query.

If either resulting \(F\)-label dimension is at most \(b\), the sign test reduces to one ordinary \(3\)-tensor isomorphism instance over \(F\), with size and construction time polynomial in the input length and \(2^b\). The same conclusion holds if the selected label space is \(E\)-linear and has \(E\)-dimension at most \(b\), with no bound on \(e\). In particular the latter bound is useful even when the \(F\)-dimension of the selected space grows. If \(r=3\), the prescribed sign is decidable in deterministic polynomial time for every additive \(K\), including arbitrary extension degree. Mismatched intrinsic algebra types give a fixed negative instance.

## Adjoints and an exterior-square quotient

Use
\[
 \mathcal A=\{(a,c):\beta(ax,y)=\beta(x,cy)\}
\]
with first-coordinate projection and involution \((a,c)^*=(c,a)\). Projection is faithful since the common radical is zero. The adjoint equations are linear. A congruence conjugates \(\mathcal A\) and preserves its involution. Finite-algebra structure algorithms at fixed characteristic recognize the hypothesis and give the simple presentation. Use a shared explicit model of \(E\) for the two algebras. [Wilson, adjoint algebras](https://arxiv.org/abs/1007.4329) · [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18) · [Lenstra, explicit finite-field isomorphisms](https://pub.math.leidenuniv.nl/~lenstrahw/PUBLICATIONS/1991b/art.pdf).

In this presentation \(U=P\otimes_E R\), where \(P=E^d\) is the natural module. One constructs the module coordinates using \(R=e_{11}U\) and the matrix units \(e_{i1}\). Since \(m=edr\) is odd, all three factors are odd. The involution on the finite field \(E\) is trivial because its order divides two. Thus on \(P\) the adjoint involution is represented by a nonsingular symmetric \(E\)-bilinear form \(b\). To see this, compose the involution with transpose to get an \(E\)-algebra automorphism of the matrix ring. Such an automorphism is inner, by transporting the matrix units and taking the images of a nonzero vector in the first diagonal position. Consequently the involution is adjunction by an invertible matrix \(B\). The involution identity forces \(B^{\mathsf T}=\pm B\), and odd \(d\) excludes the alternating option. The equations \(a^{\mathsf T}B=B a^*\) find \(B\) by linear algebra. The space of solutions is a line because any two invertible implementing matrices differ by a matrix commuting with the full matrix algebra. Equivalently, relative to one implementing matrix, every solution is scalar.

Quotient \(\bigwedge^2_F U\) by the span of
\[
 (au)\wedge v-u\wedge(a^*v)\qquad(a\in\mathcal A,\ u,v\in U).
\]
It is naturally a based-computable copy of \(C=\bigwedge^2_E R\) after choosing the above module and form coordinates. The quotient map on pure factors is
\[
 (x\otimes v)\wedge(y\otimes w)
       \longmapsto b(x,y)(v\wedge w).
 \tag{1}
\]
For a proof, take a basis \(p_i\) of \(P\) and its \(b\)-dual \(q_j\). Before taking the exterior quotient, the matrix-unit balance relations kill \(p_i\otimes q_j\) in different positions and identify all matched positions. The central entry relations move \(E\)-scalars between the two multiplicity coordinates, giving \(R\otimes_E R\), with an inverse furnished by any pair \(x,y\) with \(b(x,y)=1\). Interchanging the two original inputs induces interchange of the multiplicity factors because \(b\) is symmetric. In characteristic three the alternating quotient then gives precisely \(\bigwedge^2_E R\). The adjoint equations show that evaluation annihilates the balanced relations. Hence
\[
 \beta(x\otimes v,y\otimes w)=\psi\bigl(b(x,y)(v\wedge w)\bigr),
 \qquad
 \psi:C\twoheadrightarrow J^*.
 \tag{2}
\]
The map \(\psi\) is \(F\)-linear. It is surjective since the simultaneous evaluation was surjective. Compute it in an \(F\)-basis of \(E\)-wedges using (2) with a pair having \(b(x,y)=1\). Compute \(K=\ker\psi\) by elimination.

## Precisely which semilinear maps extend

Let \(p:U\to U'\) be a raw congruence. In common matrix-unit coordinates it has the form \(M\otimes H\), with both maps semilinear for the same \(\sigma\in\operatorname{Gal}(E/F)\). First remove coordinatewise \(\sigma\) to make the algebra conjugation \(E\)-linear. Then remove the inner matrix part on \(P\). The remaining map commutes with all matrix units and is \(1_P\otimes H_0\) for an \(E\)-linear \(H_0\). Putting back the field automorphism gives the claimed form. Preservation of the involution implies that \(M\) is a similitude, with
\[
 b'(Mx,My)=\mu\,\sigma(b(x,y))
\]
for a unit \(\mu\in E^\times\). This follows from the uniqueness up to a scalar of the form giving a fixed matrix adjunction.

Let \(N=N_{E/F}\) denote the norm and define the computable sign
\[
 \lambda=\frac{N(\det B')}{N(\det B)}\in F^\times.
\]
The determinant identity for the similitude equation gives \(N(\mu)=\lambda\): the dimension \(d\) is odd and the norm of a square is one. Since \(e\) is odd, \(N(\lambda)=\lambda\). The norm kernel in \(E^\times\) is the subgroup of squares, as follows from cyclicity. Thus \(\lambda/\mu=t^2\) for some \(t\in E^\times\). Replacing \(M,H\) by \(tM,t^{-1}H\) leaves \(p\) unchanged and makes its multiplier exactly \(\lambda\). Hence the genuine induced map on \(C\) can be written
\[
 S=\lambda G,\qquad G=\bigwedge^2_E H.
 \tag{3}
\]
It carries \(K\) onto \(K'\), and the scalar \(\lambda\in F^\times\) also preserves those two additive subspaces. This proves that \(G\) alone carries \(K\) to \(K'\).

Conversely suppose \(H\) is any \(\sigma\)-semilinear isomorphism carrying \(K\) to \(K'\) in this way. The forms \(b'\) and \(\lambda\,\sigma(b)\) have the same determinant square class, by the definition of \(\lambda\) and odd \(d,e\). Over a finite field of odd order a nonsingular symmetric form is determined by dimension and determinant square class. One elementary proof diagonalizes and splits off norm-one vectors whenever the remaining dimension is at least two. A nonsingular binary diagonal form represents one since both sets of values \(a x^2\) and \(1-b y^2\) have more than half the field elements. Then only the last one-dimensional square class remains. Thus a \(\sigma\)-semilinear \(\lambda\)-similitude \(M\) exists. The map \(p=M\otimes H\) extends \(H\) to a raw congruence by (2) and (3). On \(J^*\) the induced map is the actual quotient map of \(S\) through \(\psi\). This argument proves extension without computing a witness \(H\) or selecting its field automorphism.

## The based determinant formula

The \(F\)-determinant of \(G=\bigwedge^2_E H\) is one. The \(E\)-linear part contributes \(N(\det_E H_0)^{r-1}\), which is one because \(r\) is odd. The coefficient automorphism contributes determinant one because it has odd order dividing \(e\). Use the \(F\)-basis of \(E\)-wedges in \(C\). Let \(D\in F^\times\) be the determinant of the basis consisting of the chosen basis of \(K\) followed by any lifts of the basis dual to the supplied \(J\)-basis. Define \(D'\) in the corresponding target coordinates. Then the raw determinant of the transported map \(f:J\to J'\) is
\[
  \det f=\frac{D'}{D}\,\lambda^{\dim_F J}
           \det_F(G|_K).
 \tag{4}
\]
Indeed \(\det_F S=\lambda^{\dim_F C}\) in the \(E\)-wedge frames. In adapted coordinates this is multiplied by \(D/D'\) and equals the product of the determinant on \(K\) and the determinant on \(J^*\). The former is \(\lambda^{\dim_F K}\det_F(G|_K)\). The determinant on \(J\) is the inverse of the determinant on \(J^*\) in the dual bases. Signs equal their inverses, giving (4).

There is a second choice of carrier of dimension \(\dim_F J\). Use the annihilator \(K^\perp\) in \(\bigwedge^2_E R^\vee\) under the trace to \(F\) of the natural \(E\)-wedge pairing. This trace pairing is perfect. For a \(\sigma\)-semilinear \(H\), its semilinear dual is \(\ell\mapsto\sigma\circ\ell\circ H^{-1}\), so the pairing is preserved after trace. Its exterior action carries \(K^\perp\) onto the target annihilator exactly when the original action carries \(K\) onto \(K'\). Because \(\det_F G=1\), the determinant on the \(K\)-action equals the determinant on the annihilator action up to the computed adapted-frame ratio from the dual exact sequence. The determinant of a zero-dimensional space is one. If the selected subspace is \(E\)-linear, so is its trace annihilator, since trace nondegeneracy then identifies it with its \(E\)-annihilator.

For \(E=F\) this output is literally the prescribed orientation of alternating forms on \(R^\vee\), or on \(R\) when taking the complementary carrier. Common radicals can be removed from those form spaces without affecting any label determinants: a quotient congruence lifts by any isomorphism between radicals of equal dimension. Thus the same-field ambient dimension bound is \(r=m/d\), possibly smaller after removing a common radical. The resulting normal-form pencil can be anchored at the hyperbolic form on its quotient, with either parity of quotient dimension.

## Compiling a small defect into one ordinary TI instance

Retain \(E\) as a unital \(F\)-algebra role with multiplication and its action on \(R\). Its map is a field automorphism \(\sigma\), and the action forces the map on \(R\) to be \(\sigma\)-semilinear. Retain the bilinear exterior product \(R\times R\to\bigwedge^2_E R\) and the actual inclusion of the selected carrier \(K\). This exterior product spans the exterior square over \(F\), since \(E\)-multipliers can be moved onto either input. It forces precisely \(G\) on the exterior-square role. The analogous records work on \(R^\vee\) if using the annihilator.

If \(\dim_F K\le b\), attach the \(F\)-exterior algebra of \(K\), including its degree-one copy and top line. Its bilinear multiplication, together with the unit, forces its map to be the exterior of the linked map on \(K\). Pin the top-line multiplier to the prescribed sign divided by the known factor in (4), with the additional frame calibration if using the annihilator. Every genuine \(H\) of the desired sign extends to the entire diagram. Every diagram comparison gives such an \(H\) and consequently a raw congruence of the desired sign.

If \(K\) is \(E\)-linear and \(\dim_E K\le b\), use the \(E\)-exterior algebra instead, regarded as an \(F\)-algebra with the linked \(E\)-action. The top is an \(E\)-line with semilinear map \(x\mapsto u\sigma(x)\) in its chosen \(E\)-basis. Because \(\sigma\) has \(F\)-determinant one, its \(F\)-orientation factor is \(N(u)\). To read it, attach a copy of the top line for each Frobenius power, linked by \(x\mapsto x^{3^j}\) in the given coordinates. These are \(F\)-linear maps. Since \(\sigma\) commutes with Frobenius, the \(j\)-th copy has multiplier \(u^{3^j}\) with the same \(\sigma\). Chain field multiplication maps to multiply the coefficients and link the resulting \(F\cdot1\) line. The multiplier there is \(N(u)\) and can be pinned as in (4). This is the same linked one-line norm construction used in the maximal-subfield determinant proof.

Every record has tensor order at most three. The exterior dimensions are at most \(2^b\) over their construction field and the number and sizes of the other records are polynomial in the input. For the polynomial list of norm records, use a split coordinate algebra to mark the roles and distinguish its primitive idempotents by giving them distinct ranks in a separate module. Take direct sums of occurrence copies, tie them to their named roles by identity blocks of one linear tensor, and store the individual maps in the corresponding distinct blocks of linear and bilinear tensors. This packages the records into a constant tensor-system signature with only polynomial overhead and preserves the linked assignments in both directions. The ordinary tensor-system compiler then produces one \(3\)-tensor comparison over \(F\). A terminal vector can be specified as a linear map from a one-dimensional unital algebra role, whose map is forced to fix one. [Chen–Grochow–Qiao–Tang–Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4).

## All additive defects at multiplicity three

Suppose \(r=3\). In dual wedge coordinates, the image of an \(E\)-linear \(H\) on \(\bigwedge^2_E E^3\) is
\[
 \bigwedge^2_E H=(\det_E H)\,H^{-\mathsf T}.
\]
This is the cofactor identity, using the ordered wedge basis dual to the standard volume. Its image consists exactly of the matrices \(G_0\) of square \(E\)-determinant. Conversely, if \(\det_E G_0=a^2\), the map \(H_0=aG_0^{-\mathsf T}\) has determinant \(a\) and gives \(G_0\) under the exterior square. The square condition is equivalent to \(\det_F G_0=1\), since the \(F\)-determinant is \(N_{E/F}(\det_E G_0)\) and that norm has the square subgroup as its kernel.

Enumerate the \(e\) field automorphisms \(\sigma\). For each, carry \(K\) along coordinatewise \(\sigma\), giving \(K_\sigma\), with basis obtained by applying \(\sigma\) to the supplied basis of \(K\). The coefficient automorphism takes the wedge basis to itself and acts by \(\sigma\) on its coefficients. It has determinant one over \(F\) and on the \(K\)-basis comparison by construction. Thus the branch condition for the desired sign \(s\) in (4) is the existence of an \(E\)-linear
\[
 G_0:E^3\longrightarrow E^3,\qquad G_0 K_\sigma=K',
 \qquad  (\det_F G_0,\det_F(G_0|_{K_\sigma}))=(1,s).
\]
Here \(s\) already includes the known factor in (4). Taking or omitting the complementary carrier has the corresponding frame calibration. This condition allows an arbitrary additive subspace \(K_\sigma\).

Find a reference \(G_0\), with its actual restriction, by deterministic constructive module isomorphism over \(F\). The representation has two graded vertices \(E^3,K_\sigma\), encoded by their two projection matrices on the direct sum. Give it one loop on \(E^3\) for each multiplication by an element of the fixed \(F\)-basis of \(E\), and an arrow given by the inclusion \(K_\sigma\hookrightarrow E^3\). Present the target representation similarly with \(K'\). Use the projections and all these linear maps, extended by zero on irrelevant summands, as one list of module-action matrices. Intertwiners respect the vertex projections. The loops force \(E\)-linearity on \(E^3\), and the inclusion forces the \(K\)-map to be the restriction of that map. Thus ordinary module isomorphism is exactly strict transporter existence. The constructive Brooksbank–Luks algorithm computes the isomorphism or certifies that none exists in polynomial time on these explicit matrix lists. [Brooksbank–Luks, *Testing isomorphism of modules*, Theorem 3.5](https://ix.cs.uoregon.edu/~luks/ModIso.pdf).

For a nonempty branch, form the \(F\)-algebra
\[
 A_\sigma=\{X\in\operatorname{End}_E(E^3):XK_\sigma\subseteq K_\sigma\}.
\]
Its basis is obtained by linear equations using the multiplication loops and the actual inclusion. Its units are exactly the strict source stabilizer: if an element is invertible on \(E^3\), equality holds on \(K_\sigma\) by dimension, and its inverse preserves the subspace. All strict transporters are the reference map composed on the source with one of these units.

Compute the radical \(I\) of \(A_\sigma\) and the simple factors of \(A_\sigma/I\). On the \(I\)-power filtrations of \(E^3\) and \(K_\sigma\), the action on each quotient factors through that semisimple algebra. For the simple factor \(M_{h_j}(E_j)\), sum its simple-module multiplicities over the filtration quotients of the two spaces to obtain \(u_j,v_j\). These integers are computed by applying the factor's central idempotent on each quotient and dividing the dimension of its image by \(h_j[E_j:F]\). A unit with component \(g_j\in\mathrm{GL}_{h_j}(E_j)\) contributes
\[
 \big(N_{E_j/F}(\det_{E_j}g_j)^{u_j},
      N_{E_j/F}(\det_{E_j}g_j)^{v_j}\big)
\]
to the determinant pair. This follows from the ordinary determinant on copies of the natural simple module and multiplication over the filtrations. Units of the quotient lift to units of \(A_\sigma\) because the kernel ideal is nilpotent, and the norm and determinant maps are onto. Thus \(\big((-1)^{u_j},(-1)^{v_j}\big)\) for all \(j\) generate the entire two-sign image. Multiplying the reference two signs by this subgroup and checking for \((1,s)\) decides the branch. All algebra operations are deterministic polynomial time over the fixed prime field. As the extension degree is at most the original input dimension, the complete scan of Frobenius choices is polynomial. This also yields a polynomial-time many-one reduction to ordinary TI by outputting a fixed yes or no comparison. [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#Thmtheorem18).

## Large examples beyond the intrinsic exterior-grade test

Take \(E=F\), \(d=3\) and arbitrarily large odd \(r\). Let \(b\) be the standard symmetric form on \(P=F^3\). On \(R=F^r\), choose a two-dimensional \(K\subset \bigwedge^2 R\) whose nonzero bivectors all have rank greater than four. Use (2) with \(\psi\) the quotient by \(K\). This \(\beta\) has zero common radical, since a nonzero pure wedge has rank two and cannot lie in \(K\).

The projected adjoint algebra is exactly \(M_3(F)\) acting on \(P\). Indeed in an orthogonal basis on \(P\) an adjoint equation for each block has the form
\[
  P_{ji}v\wedge w-v\wedge Q_{ij}w\in K
\]
for every \(v,w\in R\). The left side has rank at most four, hence vanishes. For fixed nonzero \(v\) and arbitrary \(w\), wedging the identity with \(v\) gives \(P_{ji}v\in\operatorname{span}(v,w)\) for every \(w\) independent of \(v\). The intersection of these planes is \(Fv\). Thus the blocks are scalar and conversely all scalar blocks give adjoint pairs. The radical of this algebra is zero and there is a single central factor. Accordingly the previous intrinsic adjoint flag has one full ambient grade. Both \(J\)-dimension and its total exterior codimension are quadratic in \(r\), but here the oriented carrier has dimension two.

For an explicit \(K\), use four disjoint even-dimensional blocks of sizes \(6,8,10,12\) in \(R\), with nonsingular bivectors \(\omega_1,\ldots,\omega_4\) on them. Take the span of
\[
 a\omega_1+b\omega_2+(a+b)\omega_3+(a-b)\omega_4
 \quad (a,b\in F).
\]
For \(r\ge37\), the blocks fit. The four projective lines of \(K\) have distinct ranks \(30,28,26,24\). An exterior-square stabilizer fixes those lines individually and hence acts on \(K\) by a scalar, of determinant one. The multiplier \(\lambda\) is one in a self-comparison. Formula (4) then proves that all raw stabilizers have sign one. Flipping one supplied \(J\)-basis sign yields a false positively oriented comparison with the same ordinary congruence verdict. This is a genuine sign test with a two-dimensional marker on an unbounded quadratic family.

## Scope

The balancing quotient uses the actual adjoint action of the descended alternating map. The previous exterior-grade method works in \(\bigwedge^2_F U\), while the new ambient space is \(\bigwedge^2_E R\), even when the initial adjoint flag has only one large grade. The exact semilinear normalization for a simple adjoint does not require a small kernel. A small selected carrier gives the one-query conclusion. General square-zero inputs can have other adjoint types or large remaining multiplicity-space defects. The unrestricted reduction in Open Question 1.9 remains open. This is a written proof. Exact controls enumerated all \(5{,}616\) exterior-square images of \(\mathrm{GL}_3(F)\), checked the strict two-sign cosets in all four coordinate-subspace dimensions, and checked 180 cofactor inversions and semilinear orientation calibrations over \(\mathbb F_{27}\). [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
