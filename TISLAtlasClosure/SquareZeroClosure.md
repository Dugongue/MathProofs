# Exact missing lemma on square-zero matrix spaces

Let \(H\) be determinant-one dense three-tensor isomorphism over \(\mathbb F_3\) reducing to ordinary TI by a deterministic polynomial-time many-one map. The following normal form reduces the unresolved step to one ambient sign, even though every product of two operators is zero.

## The lemma

Use a symmetric bimap \(\beta:X\times X\to Z\) with zero common radical and spanned output, \(\dim X\) even and \(\dim Z\) odd. On the based space \(A=\mathbb F_3 1\oplus X\oplus Z\), multiply \(x,y\in X\) by \(\beta(x,y)\), annihilate all products involving \(Z\) and the radical, and give \(1\) its usual unit role. For \(a\in A\) let \(L_a:A\to A\) be left multiplication. Define the matrix space in \(\operatorname{End}(A^2\oplus A)\) by
\[
 {\cal S}(A)=\{N_{a,b}:a,b\in A\},\qquad
 N_{a,b}(u,v,w)=(0,0,au+bv).
\]
Both the common kernel and the sum of the images of this space are exactly the last copy of \(A\).

**Missing lemma.** Given two spaces of this displayed form which are conjugate by an invertible matrix over \(\mathbb F_3\), there is a deterministic polynomial-time map to one ordinary TI instance whose answer is YES exactly when the spaces admit a conjugator of determinant \(+1\).

This comparison has the ordinary-conjugate promise, with no requirement that a conjugator is supplied. It can equivalently be stated for the compact matrix groups \(1+{\cal S}(A)\). As \(N_{a,b}N_{c,d}=0\) for every choice, the group law on the nilpotent terms is just vector addition and every nonidentity matrix has order three. Subtracting the identity from a list of generators and taking linear span recovers the space. The reduction does not ask for equivalence of abstract abelian groups.

## Exact reflection and lift

Write \(U=A^2\), \(W=A\), and \(\mathcal M(A)=\{[L_a\ L_b]:a,b\in A\}\subseteq\operatorname{Hom}(U,W)\).
Any conjugator of square-zero spaces preserves the common kernel \(W\), and thus has diagonal blocks
\[
 Q:U\longrightarrow U',\qquad P:W\longrightarrow W'
\]
and an arbitrary lower shear. Its condition is \(P\mathcal M(A)Q^{-1}=\mathcal M(A')\), and its determinant is \(\det P\,\det Q\).

The left idealizer of \(\mathcal M(A)\) is exactly \(L_A\). Indeed if \(D\mathcal M(A)\subseteq\mathcal M(A)\), apply \(D\) to the first coordinate projection \([I\ 0]\). The result has the form \([D\ 0]\), so \(D=L_a\) for some \(a\). Conversely each \(L_a\) preserves \(\mathcal M(A)\) on the left. As a result,
\[
 P L_A P^{-1}=L_{A'}.
\]
This induces an algebra isomorphism \(\phi:A\to A'\), and evaluating on \(1\) gives \(P(x)=\phi(x)u\) with \(u=P(1)\) a unit. Normalize by \(\phi\) on \(W\) and \(\phi\oplus\phi\) on \(U\). After that normalization the block \(P\) is regular multiplication by a unit, so it preserves \(\mathcal M(A)\) by itself. Applying both coordinate projections to the normalized \(Q^{-1}\) shows that both its block rows are \(A\)-linear. Hence the normalized \(Q\) lies in \(\operatorname{GL}_2(A)\). Conversely any algebra isomorphism \(\phi\) supplies the conjugator \(\phi\oplus\phi\oplus\phi\).

The integer \(d=\dim A\) is even. A unit of \(A\) has regular determinant \(s^d=1\), where \(s\) is its nonzero scalar residue. More generally any \(C\in\operatorname{GL}_2(A)\) has determinant
\[
 \det_{\mathbb F_3}(C)=
 \det_{\mathbb F_3}(\overline C)^{\,d}=1
\]
on \(A^2\). To see this, filter \(A^2\) by the powers of its radical in each coordinate. On each successive quotient, the induced map is \(\overline C\) on each copy of the two-dimensional coordinate factor. The number of such copies over all grades is \(d\). Thus
\[
 \det P=\det\phi,\qquad \det Q=(\det\phi)^2=1,\qquad
 \det(g)=\det\phi .
\]
The ambient orientation is exactly the orientation on the common image \(W\); on the quotient \(U\) it is already one. These formulas hold for every conjugator, and both signs reflect and lift exactly.

Consequently the missing lemma is equivalent to \(H\). In detail:

1. Ordinary comparison of these spaces is equivalent to algebra isomorphism by the first calculation, and converts to ordinary TI by the multiplication tensors. Conjoining this ordinary test with the supplied promise map makes the promised reduction valid on all pairs.
2. The earlier weighted cube-zero compiler uses algebras \(A\) with exactly the two stated parity conditions, and computes any of the seven nontrivial characters on the determinant triple of an arbitrary tensor transporter. On a nonempty ordinary transporter, the sign patterns are one coset \(d_0 D_0\) in \(\{\pm1\}^3\). The identity belongs exactly when every character takes the value \(+1\) somewhere on that coset. If the ordinary transporter is empty, each corresponding weighted comparison fails. Seven applications of the lemma and one ordinary conjunction give \(H\).
3. Conversely, signed comparison of these spaces is signed algebra isomorphism. An ordinary multiplication isotopy of the algebras normalizes to an algebra isomorphism by evaluation at the units. Undoing the normalization uses only unit multiplications, whose determinants are one. So determinant-one multiplication-tensor isomorphism expresses the orientation exactly. Apply \(H\).

The zero-character version also makes the ordinary comparison on this class TI-complete. The maps use a basis of \(A\), multiplication matrices, and two copies of the domain, all of polynomial size. [Weighted characters](baseline/baseline/earlier/CubeZeroAndExtensions.md) · [Ordinary conjunction and normalized isotopy](baseline/baseline/earlier/hypoworld/ComplexityTransfers.md)

Over any fixed finite \(F\), the same argument can use \(|F^\times|\) copies in the domain, with dimension \(d\) divisible by \(|F^\times|\), as in the earlier congruence compiler. The domain contribution of \(\phi\) is then trivial and its codomain contribution remains one copy of its determinant. Over \(\mathbb F_3\) two copies suffice, and the ordinary target stays over the same field.

## A sharp local-to-global counterexample in the square-zero normal form

Take the free truncated commutative algebra \(A\) from [CommutingOperators.md](CommutingOperators.md), with \(n=\dim X\equiv2\bmod4\), and use \(A'\) with product bimap \(-\beta\). Let \(r_0:A\to A'\) negate the scalar coordinate and fix the other coordinates. It conjugates the radical multiplication spaces, and hence conjugates the full regular multiplication subalgebras. The odd ambient map \(r_0\oplus r_0\oplus r_0\) is an explicit ordinary conjugator of \({\cal S}(A)\) to \({\cal S}(A')\). All normalizers of \({\cal S}(A)\) are even by the exact reflection above and the free-algebra determinant \((\det P_X)^{n+2}=1\). Therefore there is no even conjugator of the full pair.

There is nevertheless an even simultaneous conjugator for every corresponding tuple of length \(k<n/2+2\). Work first with the centralizer of a tuple of \(k\) rows \([L_{a_i}\ L_{b_i}]\) in \({\cal S}(A)\).

- If the scalar-residue rows \((\overline a_i,\overline b_i)\) span less than two dimensions, choose a nonzero vector \((s,t)\) in their common kernel. For \(0\ne z\in Z\), the line through \((sz,tz)\in U\) is in the common kernel of all rows since \(JZ=0\). Negate this line and fix a complementary hyperplane in \(U\), acting by the identity on \(W\). This odd map centralizes the tuple.
- If the residue rank is two, select two rows independent modulo \(J\). They form an invertible \(2\times2\) matrix over the local ring \(A\). Normalize the domain action so these rows are \([I\ 0]\) and \([0\ I]\). Subtract scalar multiples of the two rows from all others to make all their entries nilpotent. Taking these linear combinations preserves the pointwise centralizer. The remaining rows involve at most \(2(k-2)<n\) regular multiplications by elements of \(J\). The small-tuple argument for the free algebra in [CommutingOperators.md](CommutingOperators.md) gives an odd linear map \(P\) on \(A\) commuting with them all. Then \(P\oplus P\oplus P\) commutes with every normalized row and is odd. Conjugating back preserves its sign.

Composing either odd centralizer element with the given odd ordinary conjugator yields an even conjugator for the chosen corresponding tuple. At length \(n/2+2\) there is a tuple for which this fails: take the two coordinate projections and the \(n/2\) rows \([L_{x_{2i-1}}\ L_{x_{2i}}]\) of a basis of \(X\). The projections make the common kernel \(W\) and force any tuple centralizer's quotient block to be \(P\oplus P\). The remaining rows make \(P\) commute with every \(L_{x_i}\), hence with the entire regular algebra. Then \(P\) is a unit multiplication and is even. This tuple therefore has no even conjugator to its reflection. The threshold \(n/2+2\) is exact, also for the corresponding group elements \(1+N\).

This supplies a concrete failure for local tuple tests even in the sharper missing lemma. It does not bound a reduction allowed to inspect the entire coefficient table.
