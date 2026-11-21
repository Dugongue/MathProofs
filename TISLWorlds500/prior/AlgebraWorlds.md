# Compatible and incompatible algebraic orientation restrictions

[Prior scalar-centroid carrier](prior/ScalarCentroid.md) · [Earlier cyclic slice comparison](prior/CyclicSlices.md)

Work over \(F=\mathbb F_3\). Write \(H\) for the deterministic polynomial-time many-one reduction \(\mathsf{TI}_{SL}(F)\le_m\mathsf{TI}(F)\). All linear spaces have ordered coordinate bases. For square-zero carriers use the earlier exact reduction to the determinant \(\det g\,\det h\) of a transporter of the symmetric radical bimap \(\beta:X\times X\to Z\), with \(\dim X\) even, \(\dim Z\) odd, spanned output, and zero common radical. The latter conditions imply \(\operatorname{Ann}_J(J)=J^2\) in \(F1\oplus X\oplus Z\). For alternating bimaps the same total sign is the permutation sign of the induced isomorphism of compact special exponent-three groups in Baer coordinates. This follows from the group sign argument in the earlier atlas. These are informal proofs. The two construction dependencies are *CubeZeroAndExtensions.md* (weighted symmetric carrier) and *CyclicSlices.md* (regular-plus-dual construction and Frobenius corrections). The new lower reductions require no conjecture or unavailable oracle; the claimed separations are conditional on failure of \(H\).

## Intrinsic slice structure

### W01. Centroid equals the right idealizer

**Unconditional.** For a symmetric or alternating \(\beta\) with output spanned and zero common radical, its centroid on \(X\) is exactly the right idealizer of its scalar form space \(S=\beta^*(Z^*)\).

Indeed, in matrix coordinates the centroid equations say \(P^{\mathsf T} B=B P\) for every \(B\in S\), and \(B\mapsto BP\) is the dual of the induced action on \(Z\). If \(S P\subseteq S\), \(BP\) has the same symmetry type as \(B\), hence \(P^{\mathsf T}B=BP\). Since \(\beta^*\) is injective by spanned output, \(B\mapsto BP\) determines exactly one map on \(Z\), so these conditions are also sufficient. Zero common radical makes projection onto the output member of the centroid injective as well. Thus the idealizer computed by linear equations is the same centroid that produces the primitive factor decomposition. [Wilson, centroid and bilinear decomposition](https://arxiv.org/abs/1005.0548)

### W02. Cyclic slice spaces and scalar centroid have an elementary intersection

**Unconditional incompatibility.** Suppose \(S\) contains a nonsingular form \(B\), and let \(C\) be its right idealizer. Then \(S=B C\) if and only if \(\dim C=\dim Z\). Consequently a cyclic slice space of scalar centroid necessarily has \(\dim Z=1\).

Since \(B\in S\), \(BC\subseteq S\), and left multiplication by \(B\) is injective. The stated criterion follows by dimension. Combine W01 with \(\dim C=1\) for scalar centroid. In the symmetric square-zero problem the one-dimensional output is a scalar nonsingular symmetric form. A reflection gives odd tangent sign while fixing the output, so ordinary and even comparison coincide, and ordinary similarity is determined by finite-field form data. Thus the earlier scalar-centroid and cyclic-slice restrictions were individually equivalent to \(H\), but their intersection does not impose any unsolved step. This is an incompatibility of restrictions, with no contradiction between their separate lower reductions. [Classical form algorithms](https://arxiv.org/html/1708.03495)

### W03. The generated ratio algebra is independent of the nonsingular slice

**Unconditional.** Let \(B\in S\) be nonsingular and \(L_B=B^{-1}S\). The associative subalgebra \(D_B=F[L_B]\) of \(\operatorname{End}(X)\) is independent of the chosen \(B\), and a bimap transporter conjugates it.

If \(B'=Bt\) is a second nonsingular slice, \(t\in L_B\) is invertible. The new span is \(t^{-1}L_B\), already contained in \(D_B\), because a finite-dimensional unital subalgebra contains the inverse of any of its elements invertible as an ambient operator. Conversely \(t^{-1}\in t^{-1}L_B\) since \(I\in L_B\), so the algebra it generates contains \(t\) and then every element of \(L_B\). The transporter statement follows by taking ratios of congruences using the pulled-back form as first slice. In particular “all ratios commute” has no dependence on supplying, ordering, or preserving a selected nonsingular form.

### W04. The centroid in a commuting-ratio model is a multiplier stabilizer

**Unconditional.** If \(D=F[L_B]\) is commutative, then the idealizer of \(S\) is exactly \(\{a\in D: L_Ba\subseteq L_B\}\). Thus commuting ratios no longer imply cyclic slices, and the centroid can be strictly smaller than the generated ratio algebra.

The relation \(S a\subseteq S\) is equivalent to \(L_Ba\subseteq L_B\). Applying it to \(I\) shows \(a\in L_B\subseteq D\). Conversely any multiplier inside \(D\) with the indicated property satisfies the idealizer equations. No basis or marked ratio relation is added to bimap comparison.

### W05. Scalar centroid forces a bound on the omitted socle

**Unconditional.** Let \(D\) be commutative local and nonsemisimple, and let a subspace \(L\) contain \(1\) and generate \(D\). If \(L\) has scalar multiplier stabilizer, then
\[
 L\cap \operatorname{Soc}(D)=0,\qquad
 \dim_F\operatorname{Soc}(D)\le \dim_F(D/L).
\]
Here assume \(D\) has scalar residue. For a nonzero \(s\in L\cap\operatorname{Soc}(D)\), multiplication of \(L\) by \(s\) lands in \(Fs\) since \(s\) kills the radical and \(D/J=F\). Hence \(s\) is a multiplier stabilizing \(L\). It cannot be a scalar, as the socle of a nonsemisimple local algebra lies in its radical. This proves both claims. In particular codimension one forces \(D\) to be Frobenius under these hypotheses. The hard construction below attains equality in the bound with unbounded socle.

### W06. Cube-zero local ratio algebras have a sharp slice-span description

**Unconditional.** Suppose \(D=F1\oplus J\) is local of scalar residue and \(J^3=0\), and \(L\) contains \(1\) and generates \(D\). Its multiplier stabilizer is scalar exactly when \(L\) is a complement to \(J^2\) containing \(1\) and \(\operatorname{Ann}_J(J)=J^2\).

The linear projection of \(L\cap J\) onto \(J/J^2\) is onto, because \(L\) generates and products of two radical terms vanish there. If the stabilizer is scalar, W05 applied to \(J^2\subseteq\operatorname{Soc}(D)\) shows \(L\cap J^2=0\). Thus \(D=F1\oplus V\oplus J^2\) with \(L=F1\oplus V\). A multiplier lies in \(L\) because it multiplies \(1\) into \(L\). Write it \(s+v\). Its products with \(V\) lie in \(L\) exactly when \(vV=0\), and \(vJ^2=0\) already. Hence the stabilizer is \(F1\oplus(V\cap\operatorname{Ann}_J(J))\), proving the equivalence. If \(J^2=0\), generation forces \(L=D\), so a scalar centroid is possible only when \(D=F\). The cube-zero radical in the later hard example is therefore the first nontrivial radical length for this local scalar-residue ratio construction.

## Exact regular-plus-dual comparisons with omitted slices

### W07. An exact ordinary transporter rule for generating slice spans

**Unconditional.** Let \(D\) be a commutative finite-dimensional unital \(F\)-algebra, and \(L\subseteq D\) a linear subspace containing \(1\) and generating \(D\). On \(X_D=D\oplus D^*\) define scalar forms indexed by \(c\in L\) by
\[
 B_c^\varepsilon((a,f),(b,g))=f(cb)+\varepsilon\,g(ca),\qquad
 \varepsilon\in\{1,-1\}.
\]
The coefficient bimap has output \(L^*\); its slices are injectively labeled by \(L\) because the regular representation is faithful and \(B_1^\varepsilon\) is nonsingular. The slice span has exact ordinary comparison
\[
  \exists\,\phi:D\simeq D',\ t\in (D')^\times\quad tL'=\phi(L).
  \tag{1}
\]
This comparison does not mark the two halves or \(B_1^\varepsilon\). The \(X_D\) dimension is twice \(\dim D\), not necessarily twice \(\dim L\).

Indeed, \(B_c^\varepsilon=B_1^\varepsilon\rho(c)\), with \(\rho(c)=L_c\oplus L_c^*\). Thus the ratio algebra is the full faithful \(\rho(D)\) by generation. An ordinary bimap transporter induces \(\phi\) by conjugacy of the intrinsic algebra in W03. The canonical \(\widehat\phi=\phi\oplus\phi^{-\mathsf T}\) lifts the full regular-plus-dual sets of slices. Remove it to obtain a \(D'\)-linear map, sending the target nonsingular \(B_1^\varepsilon\) under pullback to \(B_t^\varepsilon\) for a unit \(t\in D'\). This is because the original form pullback has parameter in \(L\), and after applying \(\phi\) still has a parameter in \(D'\). The diagonal map \(D_t=L_t\oplus I\) has this effect. Removing it leaves a \(D'\)-linear pointwise isometry of the full forms, since it preserves \(B_1^\varepsilon\) and commutes with every \(\rho(c)\). The original pullback on parameters is exactly \(\phi^{-1}L_t\), so it must map \(L'\) onto \(L\). Conversely \(D_t\widehat\phi\) realizes every pair in (1). The scalar slices are all split on their nonsingular quotients in the symmetric case, and hyperbolic alternating in the alternating case, since their diagonal polarization blocks vanish and the off-diagonal pairing is all that remains after removing its two kernels.

### W08. An exact sign formula includes the quotient of omitted slices

**Unconditional.** In W07, assume either \(\varepsilon=-1\), or \(\varepsilon=1\) and \(D,D'\) are local non-Frobenius. The total sign of the transporter attached to (1) is exactly
\[
 \det L_t\ \det\!\left(\phi^{-1}L_t:L'\to L\right)
 =\kappa\,\det\phi\ \det\!\left(\overline{\phi^{-1}L_t}:D'/L'\to D/L\right).
 \tag{2}
\]
The exact sequences use the ordered endpoint frames. The known frame ratio is \(\kappa\), equal to one when the frame of \(D\) is chosen in the order \(L,D/L\) at both endpoints.

The determinant of \(\widehat\phi\) is one. The tangent determinant of \(D_t\) is \(\det L_t\), and the output determinant is that of the dual of the pullback on \(L'\to L\). In the alternating case any pointwise residual map is symplectic and has determinant one. In the symmetric local non-Frobenius case, it is a \(D\)-linear hyperbolic isometry on \(D\oplus D^*\). The two indecomposables are nonisomorphic, and their endomorphism residues are both \(D/J\). In the semisimple adjoint quotient the two equal-weight residue factors are exchanged, so the norm determinants from one scale and its inverse cancel. The nilpotent kernel contributes one, as in *CyclicSlices.md*. This yields the first formula. For the second, take determinants in the two exact sequences for \(L,L'\). The determinant on the full algebra of \(\phi^{-1}L_t\) is \((\det\phi)^{-1}\det L_t\). All signs in \(F^\times\) are self-inverse, so the two copies of \(\det L_t\) cancel. Thus the departure from the cyclic formula is exactly the determinant on the omitted quotient, on the very same transporter.

### W09. The pointwise symmetric correction is exact on products

**Unconditional.** In the symmetric regular-plus-dual model of W07 for arbitrary commutative \(D=\prod_i D_i\), an odd pointwise isometry exists exactly when some local Frobenius factor \(D_i\) has odd \(F\)-dimension. In (2), dropping the non-Frobenius restriction therefore multiplies the possible sign set by exactly this pointwise correction group.

Every pointwise isometry of the generating slices commutes with \(D\), so it preserves its local blocks. For a non-Frobenius local block the calculation in W08 makes it even. For a Frobenius block \(D_i\simeq D_i^*\) as modules, and a nondegenerate identifying functional makes hyperbolic isometry the rank-two \(D_i\)-valued hyperbolic isometry. To see this, the \(F\)-valued equality for all arguments multiplied by \(c\in D_i\) and the nondegenerate Frobenius functional force equality of the \(D_i\)-valued pairing. Reduce modulo the radical of \(D_i\), leaving orthogonal isometries over its residue field, with two possible determinants \(+1,-1\). The regular action raises the norm of such a determinant to \(\dim_{D_i/J_i}D_i\), giving signs \(\pm1\) raised to \(\dim_F D_i\). The kernel acts by determinant one. Both signs in odd dimension are attained by the reflection in one nonisotropic free line, and even dimensions give only one. Actual pointwise maps extend independently across the direct sum. This describes the complete correction group, not just a sufficient reflection.

### W10. Frobenius ratio algebras give an ordinary subclass even without cyclicity

**Unconditional.** In the symmetric model of W07 with \(\dim L\) odd, if \(\dim D-\dim L\) is odd, every ordinarily isomorphic pair has both signs. The same holds, independently of the parity of \(\dim D-\dim L\), whenever every local factor of \(D\) is Frobenius.

For the first assertion multiply just the \(D\)-half of \(X_D\) by \(-1\), and the output by \(-1\). This self-transporter has total determinant \((-1)^{\dim D+\dim L}\), which is negative. For the second, if \(\dim D\) is even the first case applies. If it is odd then some \(D_i\) has odd dimension and W09 supplies an odd pointwise isometry. The symmetric signed comparison therefore reduces to ordinary TI on the indicated represented subclass, including proper generating spans. In particular, a non-Frobenius scalar-centroid hard example must have even omitted dimension; codimension one cannot be hard in this model. This uses the parity of a dimension difference, not an assumption that the bimap decomposes into small summands.


## Intersecting the hard structural restrictions

### W11. A radical product puts the original sign on the tangent layer alone

**Unconditional exact reduction.** Given a symmetric bimap \(\beta:X\times X\to Z\) of the original square-zero normal form, let
\[
 V=X\oplus Q\oplus Fe,\quad Q=Z,\qquad W=Z\oplus Fz_* .
\]
Build a symmetric bimap \(\gamma:V\times V\to W\) using \(\beta\) on \(X\times X\), the identity \(\gamma(e,q)=q\in Z\), the product \(\gamma(e,e)=z_*\), and zero for other blocks. Its output is spanned and its common radical is zero. The algebra \(D=F1\oplus V\oplus W\) with this radical product is local scalar-residue, non-Frobenius, with \(J^3=0\) and \(\operatorname{Ann}_J(J)=J^2=W\).

A vector with nonzero \(e\)-coordinate has a multiplication slice of rank at least \(\dim Z+1\): its products with \(Q\) span \(Z\), and its product with \(e\) has nonzero \(z_*\) coordinate. A vector with zero \(e\) coordinate has slice of rank at most \(\dim Z\). This identifies the hyperplane \(K=X\oplus Q\) intrinsically. Its restricted radical is exactly \(Q\), and \(\gamma(K,K)\) spans the old \(Z\). For a transporter of \(\gamma\), let its maps on \(K/Q,Z\) be \(g,h\) and its scale on \(V/K\) be \(s\). They give a transporter of the original \(\beta\). Evaluation \(e,q\) forces the map on \(Q\) to be \(s^{-1}h\). Hence the determinant on \(V\) is
\[
 \det g\,\det(s^{-1}h)\,s
     =s^{1-\dim Z}\det g\,\det h
     =\det g\,\det h .
\]
Conversely every \(\beta\)-transporter lifts to \(\gamma\) with \(e,z_*\) fixed and with \(h\) on \(Q\). Every such \(\gamma\)-transporter lifts grade-preservingly to \(D\) with its stated tangent determinant. These formulas preserve all attainable signs and include arbitrary shears via the intrinsic flag. Both \(\dim V\) and \(\dim W\) are even, so \(\dim D\) is odd.

### W12. The full separation survives scalar centroid and commuting ratios simultaneously

**Equivalent to \(H\).** The square-zero even-conjugator problem remains equivalent to \(H\) on the intersection of the following restrictions: scalar centroid, a split nonsingular scalar slice, commuting ratios of all slices to every nonsingular slice, and a local scalar-residue ratio algebra with cube-zero radical. In addition all scalar forms are split modulo their radicals, and a common complementary pair of isotropic subspaces exists without marks.

Use \(D\) from W11 and \(L=F1\oplus V\). It generates \(D\) and omits exactly \(W\), with \(\operatorname{Ann}_J(J)=W\). Therefore W06 gives scalar multiplier stabilizer, and W01–W04 give exactly the required scalar centroid and intrinsic commutative ratio algebra for the new symmetric bimap of W07. W07 also gives the split scalar forms and the common polarizations. The new \(\dim X_D=2\dim D\) is even and \(\dim L\) is odd.

For every new transporter, (1) supplies \(\phi:D\to D'\) and a unit \(t\) with \(t L'=\phi(L)\). Write \(s\) for its nonzero residue. The map \(\overline{\phi^{-1}L_t}:D'/L'\to D/L\) on the omitted square is \(s\) times the inverse induced square map. Its determinant has no \(s\) contribution since \(\dim W\) is even. Thus (2) leaves exactly the tangent determinant of \(\phi\), since the two copies of its square determinant cancel. W11 reflects it to the original total sign. Conversely every original transporter has a grade-preserving lift \(D\to D'\) that preserves \(L\) and uses \(t=1\), giving exactly its original sign. This proves both directions on ordinary and signed transporters.

Compose with the weighted symmetric cube-zero carrier and the square-zero operator carrier. The zero character proves ordinary TI-hardness, and the seven nontrivial determinant characters with the ordinary guard prove that a reduction for this intersection would imply \(H\). After replacement by ordinary comparisons the fixed conjunction is one ordinary TI. The reverse implication follows from the original signed multiplication-tensor comparison. This intersection is distinct from the empty-in-large-dimension intersection of scalar centroid with **cyclic** slices in W02: here the normalized slice span generates the algebra but omits its square. [Ordinary conjunction and tensor system compiler](https://arxiv.org/html/2306.03135v2)

### W13. One-mode equality and joint strictness coexist on the same inputs

**Unconditional equivalences and conditional strictness.** On the symmetric carrier of W12, each one-mode sign comparison is equivalent to ordinary comparison. Requiring \((\det g,\det h)=(+1,+1)\) is equivalent to the total positive comparison and hence to \(H\) as a collapse problem.

Both \(\dim D\) and \(\dim L\) are odd. The actual self-transporter \(D_{-1}\) multiplies one ambient half and the output by \(-1\), with simultaneous signs \((-1,-1)\). This corrects either sign alone and preserves the product. Every ordinary attainable joint profile therefore consists of complete pairs with fixed product, either \(\{(+,+),(-,-)\}\), \(\{(-,+),(+,-)\}\), or their union. The pair \((+,+)\) is attained precisely when the total is positive. Thus failure of \(H\) implies strictness of the joint sign test even on a class with unconditional equality for both individual tests. This is a simultaneous statement about the same explicitly represented pairs.

### W14. Preserving the scalar form transfers all orientation to the output

**Conditional separation with an exact unmarked comparison.** Marking the split scalar slice \(B_1\) in the construction of W12 forces \(\det g=+1\) on all transporters. The marked output-only problem remains equivalent to \(H\), while its unmarked output-only counterpart is ordinary comparison by W13.

In the proof of W07, preserving \(B_1\) forces \(\phi^{-1}(t)=1\), so \(t=1\). The canonical lifts of every seed witness preserve \(B_1\), and every marked transporter still reflects. By W08 the pointwise remainder is even, and \(\widehat\phi\) has ambient determinant one. Thus all the original total orientation survives just on the new output. Reverse reductions for arbitrary marked inputs use the scalar form as a typed linear functional, with its scalar role fixed by its multiplication and unit. Forgetting the marker restores \(D_{-1}\) and both output signs. Thus the displayed mark really changes the degree in the inequality branch, despite leaving the lower reduction's ordinary answers unchanged.

### W15. Identical labeled ranks, radicals and ratios can still give an orientation NO

**Unconditional collision.** Use the trivial-character seed of W12 and call its final bimap \(\delta\). It has all self-transporter total signs equal to \(+1\). The pair \((\delta,-\delta)\) is ordinarily isomorphic and has no total-positive transporter.

The ordinary map \((I,-I_Z)\) has negative total sign since the output dimension is odd. Every other transporter differs by an even self-transporter. For each labeled covector \(\lambda\), its form for \(-\delta\) is just the negative of the form for \(\delta\). Hence the entire labeled rank and radical functions coincide. The normalized ratios coincide as matrices, not just up to conjugacy, because both numerator and denominator are negated. The images of all scalar forms in projective space, the generated ratio algebra and its radical filtration also coincide. Every commutator of ratios is zero, so trace-commutator probes are identical even on the full covector space. This makes the compatibility theorem a counterexample to forgetting the output orientation data, without relying on any complexity hypothesis.

### W16. Abundant nonsingular slices do not make the new intersection easier

**Structural property of the exact hard family.** On the bimap of W12 the nonsingular scalar forms are precisely those outside one intrinsic linear hyperplane, and make up exactly \(2/3\) of the scalar forms. For \(c\in V\setminus\{0\}\), the singular slice \(B_c\) has rank \(2+2\operatorname{rank}\gamma(c,-)\).

For a parameter \(s+v\in L\), invertibility of its regular operator is equivalent to \(s\ne0\), since \(D\) is local with scalar residue. The set of nonunits in \(L\) is \(V=L\cap J\), an intrinsic hyperplane; the proportion follows over \(F\). For \(c\in V\setminus0\), left multiplication maps \(1\) to \(c\) in the tangent layer, maps \(V\) into \(W\) by \(\gamma(c,-)\), and kills \(W\). Thus its rank is one plus the slice rank in the seed relay. The hyperbolic scalar matrix doubles this rank. This strengthens the promise of one split nonsingular form to a dense nonsingular set and an explicit rank law. It also shows why numerous choices of nonsingular probes alone do not resolve the conditional separation.

## Alternating and compact group consequences

### W17. The same commuting scalar-centroid restrictions are hard for compact groups

**Equivalent to \(H\).** Compact special exponent-three group isomorphism restricted to the alternating version of W12 is TI-complete, with the exact even-versus-ordinary collapse equivalent to \(H\). Its commutator bimap has scalar centroid, contains a nonsingular alternating slice, and has a commuting local cube-zero ratio algebra. Both individual linear signs are ordinary tests, although joint evenness remains equivalent to \(H\).

Use \(\varepsilon=-1\) in W07 with the very same symmetric tangent relay \(D,L\). The centroid proof W01–W06 works for alternating slices as well. The pointwise step W08 is now symplectic, so it is even without needing non-Frobenius. All reflection and lifting calculations in W11–W12 are unchanged. The group inputs are compact commutator constants, and the determinant equals permutation sign on the coordinate-ordered group by the Baer formula. Reverse ordinary and weighted comparisons use the bimap as a typed tensor with the two input copies linked by an identity. The actual simultaneous sign correction in W13 also works here because scaling one half multiplies each alternating slice by \(-1\). Thus failure of \(H\) gives this strict joint-versus-individual distinction for compact groups, as well as for square-zero symmetric carriers. [Baer, central quotient groups](https://www.ams.org/journals/tran/1938-044-03/S0002-9947-1938-1501972-1/) · [Grochow and Qiao, compact-class tensor reductions](https://arxiv.org/abs/1907.00309)

### W18. Symmetric and alternating orientation give opposite answers with the same Frobenius ratio algebra

**Unconditional incompatibility.** Take \(D=F[t]/(t^5)\) and \(L=D\). Let \(D'\) be its table after conjugating the multiplication by a fixed odd linear coordinate change. Form the paired symmetric and alternating regular-plus-dual carriers of W07. Their ordinary comparisons are both YES, their ratio algebras match, and their scalar forms have the same corresponding rank data. The symmetric signed comparison is YES and the compact alternating group's even comparison is NO.

In \(F[t]/(t^5)\) a unital automorphism has \(t\mapsto a t+O(t^2)\), so in the successive radical grades its total determinant is \(a^{0+1+2+3+4}=a^{10}=1\). Thus all relative algebra isomorphisms to the odd conjugate table have determinant \(-1\). In the alternating cyclic carrier W08 with \(D/L=0\) and matched frames gives exactly that sign. In the symmetric carrier an odd Frobenius block supplies an odd pointwise reflection by W09, correcting the relative isomorphism. Both scalar matrices have rank \(2\operatorname{rank}L_c\) for the corresponding element \(c\); the distinction is entirely in the adjoint sign correction. Hence transferring positive Frobenius correction from the symmetric model to the alternating one would be false, even though both models carry the full difficulty on the common non-Frobenius family.


### W19. Even automorphisms are transitive on the whole nonsingular slice set

**Unconditional property of the same hard family.** In both the symmetric and alternating models of W12 and W17, every nonsingular scalar form is the pullback of \(B_1\) by a total-even self-transporter. Thus even and ordinary comparison can each be restricted to sending any one specified nonsingular scalar form to any other chosen nonsingular scalar form at the corresponding endpoint, without changing the yes/no answer.

Let the desired parameter be \(s+v\), with \(s\ne0\) and \(v\in V\). Put \(t=s+v+s^{-1}v^2\). Define an algebra automorphism \(\phi\) of \(D\) fixing the unit and \(W\) and acting on \(V\) by the shear \(x\mapsto x+s^{-1}vx\). Products of two radical elements are unchanged since \(W\) annihilates the radical. Now \(t=\phi(s+v)\), and \(tx=sx+vx=\phi(sx)\) for \(x\in V\). Hence \(tL=\phi(L)\) and \(\phi^{-1}(t)=s+v\). Equation (1) gives the indicated self-transporter. Its tangent map is the identity, hence the total sign is \(+1\) by the cancellation in W12 and W17. If an arbitrary ordinary or even comparison exists, it sends a specified nonsingular form to a nonsingular form. Compose with these even stabilizer maps to obtain the specified correspondence. This compatibility does not make the remaining output sign easy, since the marked restrictions already have the full degree in W14.

Together the results give actual coexistence in the negative world: commuting normalized slices, scalar centroid, a local ratio algebra and abundant nonsingular forms can all hold in a strictly separated class. They coexist with ordinary comparison sufficing on its individual sign restrictions and in the symmetric Frobenius classes. The proofs do not decide \(H\).


## Bounded controls

A relay with a two-dimensional tangent and one-dimensional output was checked on all 81 tangent vectors for the rank gate. On the resulting seven-dimensional algebra, all 243 normalized slice parameters were tested as multipliers of the span and precisely the three scalars survived. For the nonsingular probe transitivity, all 162 parameters \(s+v\), \(s\ne0\), had the stated shear and transported the unit slice to the requested parameter. Direct substitution checked 7,938 products for these shears and 8,624 symmetric and alternating bimap transport equations. These checks supplement the informal proofs.
