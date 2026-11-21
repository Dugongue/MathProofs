# Orientation from quotient volumes and finite probe families

Write \(A=\mathrm{TI}_{\mathrm{SL}}(\mathbb F_3)\), \(B=\mathrm{TI}(\mathbb F_3)\) and \(H=(A\le_m^P B)\). All compilers below have a single ordinary TI output. A **probe family** is a list of distinct covectors, tuples, or projective points of polynomial total size. A supplied family is part of a marked problem. To solve the underlying unmarked problem the algorithm obtaining the family must commute, as a set, with **every** original transporter. “World” entries state what follows in each branch, with additional hypotheses made explicit.

## The quotient-volume compiler

### V01. Exact typed implementation of a finite unordered family

For a family \(S\) of covectors on \(W\), introduce \(E=F^S\) with coordinatewise multiplication. Its primitive idempotents \(e_s\) are permuted by every algebra isomorphism. The linear map \(E\to W^*\), \(e_s\mapsto s\), forces that permutation to be induced by the original contragredient map. Put the original tensor and all evaluation data in the same typed system. A tuple of probes uses one map per position and a single permutation on the tuple set. All original transporters respecting \(S\) lift. Pairings into a pinned scalar line force dual actions. The tag packing in the previous atlas reduces any polynomial-size typed system of maps, products and tensors of order at most three to ordinary TI. [Typed-system theorem](https://arxiv.org/html/2306.03135v2#S4)

### V02. Components with their own linear maps

Given in addition subspaces \(K_s\subset X\) mapped to \(K'_{\pi(s)}\) by every compatible original witness, add \(K=\bigoplus_s K_s\) as an \(E\)-module, with the linear map summing their inclusions into \(X\). Any extended map acts by the original restriction on each component, because the map to \(X\) is injective on each \(K_s\). Every original witness has that extension even when the images of different \(K_s\) overlap. This implements variable kernel spaces attached to probes without fixing arbitrary labels for them.

### V03. Logarithmic fibre determinant lines

For each \(K_s\) of dimension \(r_s\), introduce all grades of its exterior algebra with the wedge maps and the degree-one identification from V02. A split \(E\)-module multiplication and fixed rank idempotents give the correct grade and fibre ties, and generation in degree one forces the action on every grade. The cost is polynomial in \(\sum_s 2^{r_s}\) and the original input. Rank zero uses its canonical scalar line. Products of two fibre lines use a bilinear surjection from componentwise simple tensors to a new \(E\)-module. Pin a vector of that line module once. These marks remain unordered under the simultaneous permutation. No exterior power on the whole \(X\) is used.

### V04. A rectangular probe exports the product of the two ambient determinants

Let \(B_s:U^*\times V^*\to F\) be the contraction at \(s\) of a framed tensor. In each endpoint take ordered bases of the two kernels, followed by quotient representatives. Their full coordinate determinants in the raw dual frames are \(\delta_U,\delta_V\). The induced square pairing of the quotients is nonsingular, with matrix \(Q_s\). In the product of the two top kernel lines use the vector with coordinate
\[
m_s=\frac{\det Q_s}{\delta_U\delta_V}.
\]
The empty determinant is one. On a witness, write \(a_U,b_U\) for the determinants on the kernel and quotient of the contragredient map, respectively, in these bases. Write \(a_V,b_V\) in the other mode. Then
\[
a_Ub_U=\delta_U/(\det(g_U)\delta_U'),\quad
a_Vb_V=\delta_V/(\det(g_V)\delta_V'),\quad
\det Q_s=b_Ub_V\det Q'_{\pi(s)}.
\]
Consequently \(a_Ua_Vm_s=(\det(g_U)\det(g_V))^{-1}m'_{\pi(s)}\). This also shows independence from adapted frames by taking identity transports. The assembled vector is nonzero for any nonempty family. Prescribe the product determinant \(c\) by pinning the source vector to \(c^{-1}\) times the target vector. V01–V03 lift every allowed witness and reflect precisely the character constraint. Both deficiencies may be logarithmic even when the ambient dimensions and the rank are unrestricted.

### V05. An alternating probe exports a single ambient determinant

For a framed alternating bimap, use the radical of the scalar form and its nonsingular alternating quotient. Put \(m_s=\operatorname{Pf}(Q_s)/\delta_U\) in the top radical line. If \(b_U\) is the contragredient quotient determinant, \(\operatorname{Pf}(Q_s)=b_U\operatorname{Pf}(Q'_{\pi(s)})\). This identity follows by matching expansion on integral polynomial matrices and hence holds over the finite field without dividing by any factorial. Alternatively alternating Gaussian elimination proves the congruence law and computes the Pfaffian using only nonzero pivots. Thus \(a_Um_s=\det(g_U)^{-1}m'_{\pi(s)}\) and the same construction imposes the single sign of \(g_U\). [Pfaffian congruence and adjugate identities](https://arxiv.org/abs/2008.04247)

### V06. Projective rectangular probes and the rank correction

For a projective set, replace the evaluation map by the sum of inclusions \(\bigoplus_s\ell_s\to W^*\), with its split \(E\)-module structure. The induced fibre scalar \(\eta_s\) sends the chosen representative to \(\eta_s\) times the target representative. The equalities in V04 now read \(\det Q_s=\eta_s^{k_s}b_Ub_V\det Q'_{\pi(s)}\), where \(k_s\) is the rank. The kernel product mark has the extra factor \(\eta_s^{k_s}\). Attach the dual of the \(k_s\)-fold tensor power of the probe line, and use the dual of its chosen representative to that power in the pinned vector. Its map supplies exactly \(\eta_s^{-k_s}\). Construct the power in a chain of line products on each rank stratum. This removes all projective scaling, even at odd rank.

### V07. Projective alternating probes and the half-rank correction

In V05 the factor is \(\eta_s^{k_s/2}\) because the Pfaffian has degree \(k_s/2\) on a rank \(k_s\) quotient. Use the dual of that power of the probe line. The correction applies even when \(k_s\equiv2\bmod4\); the result depends on the projective orbit, independently of an arbitrary lift of each line.

### V08. Simultaneous measurement, with a certified sign repair

Attach any finite list of available character measurements to the same tensor system. Thus a witness must pass all tests at once. Over \(\mathbb F_3\), express the characters as rows of \(M\) over \(\mathbb F_2\), on the \(d\) determinant bits of the acting maps. If given actual computable source self-witnesses whose sign vectors span \(\ker M\), then a witness with target measurements \(M c\) extends to one with target sign bits \(c\) by right multiplication. Conversely a witness of bits \(c\) passes the measurements. This is a sufficient one-query compiler for the entire constrained problem, and it still works without repair if \(M\) has full column rank.

### V09. Determinants from logarithmic-width invariant flags

The top line on a fibre in V03 may be replaced by the product of determinant lines of the successive quotients of an arbitrary supplied invariant flag in that fibre. Attach each subspace by inclusion and each quotient by projection. The forced action on the product is the ambient determinant by block triangularity. Adapted raw bases calibrate the two lines by the explicit determinant of their change of basis. Cost depends on the sum of exponentials of **graded** widths, so the total radical dimension may be linear in the input.

### V10. A bounded-field extension with small relative width

If an \(E_s\)-field action is marked on each kernel fibre and respected semilinearly, take the relative exterior top line over \(E_s\). Frobenius twists and multiplication give the field norm of the relative determinant. The determinant of the field automorphism on the ambient ground-field kernel is its determinant on \(E_s\) raised to the relative dimension. In a normal basis the generator Frobenius permutes the basis cyclically, so its \(j\)-th power gives \((-1)^{j([E_s:F]-1)}\). This factor is trivial for odd extension degrees or even relative dimensions. In the remaining case choose a normal element in a common finite-field model, and mark its Frobenius orbit by \(E_0=F^{\mathbb Z/e\mathbb Z}\), \(e=[E_s:F]\), sending the \(j\)-th primitive idempotent to the \(j\)-th conjugate. The inducing field isomorphism acts by shift. A linear map \(E_0\to F^{\mathbb Z/2\mathbb Z}\) sending a primitive idempotent to its index modulo two forces the induced shift on the parity algebra. Its difference line gives the automorphism sign. Use the same normal-element data in the common model on each equal-field stratum. The cost is polynomial in field representation size and exponentials of relative widths. [Finite-field algorithms](https://mat.uab.cat/~masdeu/research/notes/FinFieldsLenstra.pdf)

### V11. Exact multi-output characters

Replace \(F^\times\) by its cyclic coordinates for any fixed finite field. V04–V07 impose exact character values in \(F^\times\), not just quadratic characters. The linear repair test in V08 becomes the subgroup generation problem in \((\mathbb Z/(|F|-1))^d\), solvable by integer linear algebra. If the induced quotient is checked explicitly and its kernel generated by actual source witnesses, arbitrary joint prescribed determinants reduce to one query.

### V12. No recognition oracle is needed on promised input formats

Each procedure above computes frames, finite algebra tables, exterior products and marks by explicit operations on given probe, kernel and flag data. On a structural promise that there is an equivariant polynomial-time method of obtaining those data, it runs that method directly. Equality of size, rank stratification and graded multiplicities is necessary for any transporter in this category and mismatches can be mapped to fixed ordinary NO. No decision step deciding whether an **unmarked** family satisfies its invariance promise is used.

## Concrete reductions and comparisons

### V13. Rectangular pencils at arbitrary rank imbalance below the logarithmic threshold

A marked full-column-rank rectangular slice of size \((n+r)\times n\) with \(r=O(\log L)\) suffices for the product of the two mode determinants. Its first kernel is \(r\)-dimensional and the other is zero. The actual row-space map need not fix any complement. V04 includes both the quotient calibration and the induced action on the actual left radical.

### V14. Odd-dimensional alternating carriers

An alternating slice of size \(2m+1\) and rank \(2m\) exports the single sign by a one-dimensional radical mark. The top Pfaffian of the full slice is identically zero, but the mark in V05 is nonzero. A supplied projective slice-line uses V07 and imposes no spurious constraint on the action on that line.

### V15. Widely varying radicals and no common low-dimensional kernel

Let \(S\) be the full list of lines in a specified \(O(\log L)\)-dimensional covector subspace. Select the lines whose contractions have the required small coranks, which is a transporter-invariant filter. Apply V06 to the nonempty resulting set. The span of all radicals can be the whole mode and no common complement is required. For example, the alternating cross-product matrices in size three have one-dimensional radicals indexed by all projective probes in the full three-dimensional covector space.

### V16. Unmarked inputs with logarithmic probe mode

When the relevant whole dual mode has dimension \(O(\log L)\), enumerate all probes and select those of highest rank. The family is intrinsic and enumeration is polynomial over the fixed field. If the maximal-rank kernel widths fit V04 or V05, this gives one query on the original unmarked input. This includes the case where every slice is singular and all maximal-rank slices have distinct radicals.

### V17. Explicit color classes of probes

For multiple disjoint intrinsic probe subsets, attach their characteristic idempotents. Exact marks on one class suffice for a scalar measurement, while marks on different classes may check different characters of the same witness. Class cardinalities need not be odd, as nonzero in a single fibre already reflects the scalar equality.

### V18. Probe selection by a supplied incidence system

Suppose polynomially many lines occur as the outputs of a supplied linear incidence structure whose maps are part of the ordinary comparison. Include those lines all at once as the image set, deduplicating equal lines. The typed system sees line equality via the original injections, and the induced transporter acts on the sets without choosing an ordering. Thus a polynomial incidence presentation can replace a supplied list with no change in the signed answer.

### V19. A scalar character from a contraction of tensor products

Several compatible tensor copies can share mode maps, and take a contraction pairing on tensor products. Introduce the tensor product spaces with their universal bilinear maps so the action is forced. If a mode of dimension \(n\) is repeated \(k\) times, its tensor-power determinant is \((\det g)^{k n^{k-1}}\). A quotient-volume mark on the induced pairing therefore measures the corresponding product of exponents. For fixed \(k\) this remains polynomial, even with arbitrary original dimensions. Over \(\mathbb F_3\) a mode of odd dimension repeated an odd number of times retains its sign.

### V20. A scalar character from bounded exterior powers

On an explicitly representable \(\Lambda^k U\) the determinant is \((\det g)^{\binom{n-1}{k-1}}\), proved on diagonal matrices as a polynomial identity for generic matrices, or on elementary generators of \(\mathrm{GL}_n\). A probe on that space and another mode constrains an actual ambient sign when the exponent is odd. In particular, the exterior square of an even-dimensional space retains the sign and the exterior square of an odd-dimensional space has trivial determinant character.

### V21. A scalar character from bounded symmetric powers

On \(\operatorname{Sym}^k U\) the determinant exponent is \(\binom{n+k-1}{k-1}\), by counting one coordinate's total multiplicity across degree \(k\) monomials. Upper triangular elementary generators act with diagonal ones. A symmetric-square probe retains the determinant when \(n\) is even, whereas higher fixed powers can retain it in other congruence classes, such as \(k=3\) and \(n\equiv0,1\bmod4\).

### V22. Full single-mode conjugacy from an alternating low-corank derivative

For a matrix-space conjugacy problem, suppose a compatible construction attaches an alternating form on the same ambient space, with an intrinsic polynomial family of probes, each giving a logarithmic radical-width bound. Then V05 or V07 prescribes determinant \(+1\) of the original conjugator by one ordinary TI instance. Since the same conjugator acts on the original matrix space and on the attached form, this applies to marked congruence relations and to a derived form preserved by every original conjugacy, each with its indicated input convention.

### V23. Full three-mode reduction from two independent pair measurements and a repair

For three modes, suppose V04 can measure all pairwise products and there is a computable ordinary source stabilizer odd in all three modes. The measured pair characters have rank two and their kernel is generated by the all-odd sign. V08 gives full sign removal. A stronger condition with a third independently compiled odd-weight character gives full sign removal without a repair witness.

### V24. One independent alternating measurement completes two pair tests

If the measured characters are \(x_1+x_2\), \(x_2+x_3\) and \(x_2\) in additive sign bits, their rows form a basis. A V05 measurement on a tied alternating structure provides the third row. This is a theorem about the existence of a **joint** ordinary witness with all three prescribed signs, even if each standalone test admits multiple witnesses.

### V25. Determinant-one on a chain complex with small homology

For finite chain complexes with specified chain maps as witness, the alternating product of determinants on chain groups equals the alternating product on homology. Split each chain space into incoming boundaries, homology representatives and outgoing lifts. The boundary determinant occurs twice with opposite powers via its natural identification with the outgoing quotient of the neighboring chain group. Raw-frame changes give computable endpoint scalars. Attach homology spaces by cycle inclusions and quotient projections and pin their product determinant lines, using duals in odd degree. If all homology widths are logarithmic or are flagged as in V09, this compiles the alternating character in one TI query, with no chain group width bound.

### V26. Relative signs of two chain maps

Given chain complexes \(C,D\) and an explicitly marked chain map \(f:C\to D\), include its mapping cone by the standard block differential and forced summand maps. The cone's alternating character is that of \(D\) divided by that of \(C\). V25 compiles equality of these characters from small cone homology. In particular \(f\) a quasi-isomorphism makes the character ratio an explicit endpoint scalar even if neither complex has small homology.

### V27. Joint constraints from long exact sequences

For an equivariant exact sequence of arbitrary length, the alternating product of induced determinants is a computable endpoint scalar, proved by cancelling successive image determinants. When certain terms admit independently attached volume marks, one may eliminate their rows from an arbitrary joint determinant problem by linear algebra as in V08. This assembles constraints across layers without treating their witnesses as independent.

### V28. Differentials into dual mode spaces

For a two-term complex \(U^*\to V\) given by a chosen compatible rectangular map, the alternating ambient character is \(\det(g_U)\det(g_V)\), up to an overall choice of chain parity. The kernel and cokernel are its only homology. V25 recovers V04 and also composes it with higher differentials having the same original mode maps. This provides a way to replace a single large kernel by smaller homology with an explicit incoming differential.

### V29. A conditional polynomial-time algorithm on each compiled subclass

If ordinary ternary TI lies in P, each subclass in V13–V28 is decidable in P, including exact agreement of all its compiled characters. The proof is composition with the single query. It applies even when the strict world and ordinary TI in P are hypothesized together because the subclass theorem is unconditional. This narrows what a superpolynomial signed lower bound would have to use in that joint world.

### V30. Uniform independent hybrid families

Take a polynomial list of independent carrier comparisons. On each, use any eligible mark to implement all local candidate character profiles by ordinary TI. The earlier finite-abelian switch compiler imposes arbitrary linear constraints on the resulting profile choices in one query. This applies to heterogeneous probe and complex models, because local profile sets are cosets of subgroups and all transporters in separate inputs are independent. [Abelian switch compiler](prior/prior/earlier/baseline/baseline/LinearSwitchCompiler.md)

### V31. A connected network of tied probes

When polynomially many systems share some mode maps, assemble them as a single typed diagram with those shared spaces. Multiply or dualize character lines to impose linear equations on their products. Reflection now gives common maps on every shared mode; a collection of unrelated local witnesses would not suffice. The size is polynomial in the total marked data and the result again contains one ordinary TI query.

### V32. Ordered Lagrangians on split symmetric quotients

A symmetric quotient of dimension \(2m\) with a specified Lagrangian has a hyperbolic basis extending any basis of that Lagrangian. A transporter preserving the Lagrangian acts on it and the complementary quotient by \(D\) and \(\eta^{-1}D^{-t}\), where \(\eta\) is the projective probe scalar in V06. Thus the quotient determinant is \(\eta^{-m}\) in hyperbolic bases. Attach the small radical line and the dual of the \(m\)-fold probe line, with raw-frame calibration \(1/\delta_U\). The result prescribes the single original determinant, for arbitrarily large split symmetric quotients. The Lagrangian is marked by its inclusion into the quotient.

### V33. Unordered complementary Lagrangians

If the marking gives an unordered pair of opposite Lagrangians, use their finite two-point algebra and inclusion maps as in V01–V02. An exchange of the two \(m\)-dimensional summands has determinant \((-1)^m\). The one-dimensional difference of their two primitive idempotents carries the exchange sign, so its \(m\)-fold power supplies that scalar to the line in V32. This yields the full ordinary compiler even when odd exchanges are allowed.

### V34. A marked isotropic subspace with small middle quotient

For a general symmetric form modulo its radical and an indicated isotropic \(I\) of dimension \(k\), use the filtration \(I\subset I^\perp\subset Q\). On the hyperbolic outer layers the determinant product is \(\eta^{-k}\), by the induced pairing, and the middle layer is \(I^\perp/I\). Compute the ambient character from the small original radical line, the determinant of the middle layer, the dual of the \(k\)-fold probe line and frame calibration. This proves the compiler if the middle quotient and radical have logarithmic widths. It includes marked Witt decompositions with anisotropic middle spaces of dimensions one and two. No isotropic subspace is presumed invariant on an unmarked input.

### V35. Large radicals with small cohomology of a supplied complex

In the V04 or V05 diagram a radical \(K_s\) may be the first term of a polynomial-size equivariant complex. V25 expresses its determinant through the other chain spaces and the small homology lines. When the other spaces have available character lines, use their signed product in place of \(\det K_s\). An equivariant presentation by tight exact sequences is enough, with no width bound at any intermediate kernel. The same construction works fibrewise with \(E\)-linear maps.

### V36. A change of bases is not an extra hypothesis

In V32–V35 arbitrary source and target frames determine raw ratios as in V04. For a checkable example, a hyperbolic quotient with ordered \(I\) always has proper self-isometries, but mapping to a raw odd-basis reflection has negative determinant on every available isometry. The endpoint ratios detect exactly this negative coset even though both hyperbolic signatures are the same.

### V37. A nonsingular symmetric slice alone does not give a single determinant line

For \(Q=I_n\) over \(\mathbb F_3\), both \(I_n\) and \(\operatorname{diag}(-1,1,\ldots,1)\) are self-isometries. For a nonsingular alternating form every isometry is proper by V05. Thus a paired proposed theorem treating the two forms identically is false, while the flagged symmetric versions V32 and V34 remain valid. The two examples concern allowed witnesses and give no computational lower bound.

### V38. Large explicitly split étale coefficient algebras on probe lines

Fibrewise extensions over a fixed finite field can be grouped by their residue degrees, and represented as split products of the finite field models. Any transporters may permute equal-field factors. If a relative basis degree occurs in the **kernel**, its norm-level line is formed using multiplication and Frobenius in the finite product. The resulting ground-field fibre display includes the same permutation of fibres already forced by V01. There is no need to bound the number of product factors. This generalizes V10 from a single marked field action on the underlying whole mode.

### V39. Small semilinear projective point orbits

V06 also works when probes and spaces are transported semilinearly over a fixed extension and the coefficient automorphism is tracked in the diagram. Take norms of the character values before comparing scalar lines over the prime field. Norm is equivariant under every field automorphism and respects the correction factor. This imposes the norm of the linear part's prescribed character. If the determinant of the full ground-field witness is intended, include the Frobenius sign from V10 and the exponent for its ambient dimension.

### V40. A paired world for polynomial projective probe enumeration

For a fixed effective carrier family that is H-hard by a sign-preserving Karp map, suppose there is a polynomial, equivariant selector of a nonempty projective probe family with kernel flags and enough measurements for V08. This world implies \(H\). Its negation only says this selector program fails, while \(\neg H\) forces it to fail on at least one part of its promised coverage. The hypothesis needs an actual construction of the selector and the marks.

### V41. A paired world for its orbit-list size premise

If an intrinsic probe orbit contains at most \(L^c\) points and generators of its action and one member are computable, breadth-first orbit enumeration yields a polynomial list. For unmarked inputs the resulting set must additionally be transporter-equivariant across endpoints. Without the size bound the same enumeration has no polynomial guarantee, yet any smaller equivariant qualifying set still suffices by V06. This separates the small-orbit conjecture from a uniform enumeration conjecture.

### V42. A paired world for eigenspace flags

If a canonical, transporter-invariant commuting endomorphism has all primary subquotients of dimension \(O(\log L)\), its primary flag followed by the powers of each primary polynomial is an explicit volume algorithm. Factor the characteristic polynomial over the fixed field, order its monic factors by the common field model, use the primary kernels, and apply V09. A proposed blanket bound implies \(H\) only on an H-hard family with the needed measurements. Its failure leaves open the possibility that the oversized subquotients have even multiplicity and do not contribute their sign.

### V43. A paired world for actual auxiliary symplectic structures

A polynomial-time covariant alternating form on the whole relevant ambient space, with a logarithmic radical and the required fixed or equivariantly tracked scale, would give a direct ordinary determinant-one compiler by V05. If such a family of forms does not exist, a derived form on a linked quotient with small determinant line for its kernel still suffices. Thus strictness excludes universal successful coverage of this form on any H-hard square-zero carrier, even if the underlying ratios commute.

### V44. A paired world for functorial homological detection

If complexes in V25–V28 with logarithmic-width homology generate the needed determinant characters on a complete H-hard test family, ordinary TI suffices there. If no such construction works, \(H\) can still hold via reductions outside this construction. This implication uses actual polynomial-size, lift-and-reflect complex data. Near-exactness stated only as equality of homology dimensions does not imply the existence of the required equivariant complexes.

### V45. A paired world for polynomial recovery from reductions to GI

Suppose an ordinary encoding into graphs has a polynomial-time map from **every** graph isomorphism to an original transporter, an explicit lift for every original transporter, and the constraint characters can be evaluated on returned witnesses. Then GI search recovers one transporter and generators for the source stabilizer. Obtain graph generators by ordinary GI individualization and a stabilizer chain. Apply the sign character to the lifted generators when the decoding is a group homomorphism on self-maps, or use a supplied surjective homomorphism on that group. With GI in P this decides the signed source language in P. Bare language reducibility to GI provides only decision, so its truth branch alone supplies none of these lifts or homomorphisms.

### V46. A paired world for graph canonization without full transporter lift

Suppose instead graph canonization supplies only, for each individual encoding, a decoded original map to a common **ordinary** canonical representative. The comparison yields one original transporter. To obtain determinants, it suffices additionally to compute any generating set of the determinant image of that representative's source stabilizer. If such an image summary cannot be recovered from the canonical representation, ordinary canonization alone provides no certified orientation test. This differs from V45, which uses the entire graph automorphism group.

### V47. A paired world for polynomial automorphism identification

An algorithm computing generating witnesses for each original source stabilizer, together with a witness finder for ordinary TI, decides signed ternary TI by Gaussian elimination on the eight-element sign group. Under the proposed algorithms \(H\) follows. If stabilizer generators are expensive, their eight-element sign image could still be computed directly. In particular the strict world forces a failure of at least one of the two proposed algorithms, even though it does not imply that counting automorphisms is hard on every instance.

### V48. A paired world for canonical labels of the quotient by orientation

Suppose a polynomial algorithm gives each tensor a canonical **signed** label and recovers a signed transporter to a common label representative. Equality decides signed TI, hence \(H\). If signed canonization is superpolynomial, the sign decision problem can still reduce to ordinary TI. The direction is irreversible without an additional canonization-from-decision theorem for the action. On the compiled probe classes above, a signed decision solver alone only decides their relation.

### V49. A paired world for randomized generator recovery without derandomization

If a randomized expected-polynomial ordinary algorithm recovers a correct witness and a full source stabilizer generating set with a **verifiable stopping certificate** and always terminates almost surely, the sign computation gives signed TI in ZPP. Together with P=ZPP this forces \(H\). If P differs from ZPP, that argument concludes the randomized bound alone. Merely verifying each reported generator is insufficient to certify generation, which is why a full-generation certificate or an always-correct algorithm is part of the premise.

### V50. A paired world for approximate or exact low-dimensional extraction

Suppose a proposed covariant algorithm computes orbit signatures that refines all three characters and is complete for signed orbits. Computing and comparing these signatures in polynomial time would give \(H\). If its completeness has only a bounded false-merge probability on pairs and never falsely separates YES, it gives a randomized signed decision algorithm, with an extra derandomization premise needed for \(H\). V01–V08 avoid this distinction because the exact marker check keeps the original transporter condition.

### V51. A paired world for randomized versus deterministic bounded carriers

On any H-hard carrier using only explicitly given probe formats, a uniform randomized P-time equivariant data extractor with success at least \(2/3\) for each pair would give a one-output randomized reduction if success means the compiled instance has the right answer. If the extractor instead merely claims to find a probe whose **ranks** are correct, it need not be equivariant and the implication does not follow. A logarithmic seed list with either verifiable success or a majority of valid outputs can be combined by the ordinary aggregation theorem to imply \(H\). [Ordinary aggregation](prior/prior/earlier/baseline/baseline/LinearSwitchCompiler.md)

### V52. A paired world for symplectic versus orthogonal generation

Every isometry of a nonsingular alternating form is proper, so a supplied faithful covariant alternating realization of the entire action on the ambient space automatically fixes the stabilizer determinant. The analog for the full orthogonal group is false by V37. If the proposed realization is instead into a proper orthogonal model with marked isotropic subspace, V32 or V34 can give a compiled determinant character. Group generation by small good elements is not needed for this sufficient branch.

### V53. A paired world for positive characteristic invariant theory

If invariant evaluations separate rational signed orbits and can be computed completely in polynomial time, they give a decision algorithm and \(H\). Finite generation of the algebraic-group invariant ring does not itself imply rational orbit separation, and slice-polynomial routines evaluating only geometric invariants cannot distinguish a rational sign twist when the two tensors are in the same geometric signed orbit. The explicit quotient-volume tests over a finite ground field operate in their stated typed category and use the original equality equations.

### V54. A paired world for subexponential global algorithms

A quasipolynomial or subexponential algorithm for signed TI alone implies the same upper bound for each of its compiled subclasses and is compatible at the level of logic with failure of **polynomial** Karp reducibility. A polynomial algorithm for signed TI forces \(H\), by outputting a fixed ordinary YES or NO instance. Conversely if ordinary ternary TI is in P and \(H\) holds, signed TI is in P. This paired comparison prevents using a weaker asymptotic exponent as a contradiction in the strict world.

## Combining quotient measurements with oriented boundary tests

### V55. A subgroup boundary compiler

Let \(D=(\mathbb F_2)^d\) be the fixed determinant-bit group of a transporter problem with computable diagonal reflections. Let \(h:D\to Q\) be a fixed quotient homomorphism with kernel \(W\). For a pair \(x\), let \(P_x\subset D\) be its attainable determinant profile. Assume a single ordinary TI instance tests \(P_x\cap W\ne\varnothing\). For each member \(w\) of a generating set of \(W\), suppose a deterministic polynomial test, on ordinary-YES pairs only, decides whether \(0\notin P_x\) and \(w\in P_x\). Then exact membership \(0\in P_x\) reduces to one ordinary TI instance.

Apply the testers to all reflections in \(W\), at both endpoints of each generator edge. This labels every changing edge with its endpoint bits and certifies equality on every other edge on the ordinary-YES promise. If there is a changing edge, traverse the connected Cayley graph of \(W\) from that labeled edge and propagate the bits. Output the quotient query when the recovered zero bit is one and fixed NO when it is zero. If no boundary appears, use the quotient query itself, because the bits on \(W\) are constant. On ordinary-NO pairs the quotient query and fixed NO are both false, so arbitrary out-of-promise behavior cannot cause false acceptance. The proof works even without the fact that \(P_x\) is an affine subspace.

### V56. A single fragile direction completes two quotient measurements

In three modes over \(\mathbb F_3\), let \(W\) be generated by \((1,1,1)\). On a carrier covered by V04 with two independent pair measurements, the check \(P_x\cap W\ne\varnothing\) is the joint ordinary marked query. One oriented difference tester for the all-odd reflection therefore completes the full signed comparison. The tester only needs to distinguish the orientation \(0\to(1,1,1)\) on ordinary-positive inputs. No full transporter finder is assumed.

### V57. A single weight-two direction can suffice with a total-sign mark

Suppose a family of three-mode comparisons is closed under mode permutation, and existence of an even total-sign witness on the family has an ordinary compiler. Take \(W\) to be the even-weight plane. An oriented two-mode difference tester for the first pair yields testers on every pair of modes by permutation. Their directions generate \(W\), so V55 gives the full signed comparison. This identifies a sufficient condition involving a different restricted promise than the one-mode difference result in the complexity chapter.

### V58. A cyclic determinant variant

For a fixed nonbinary field, write the determinant group multiplicatively and take generating steps of any specified subgroup \(W\). Test both a generator and its inverse, because an edge of its Cayley graph need not be involutive. The same proof as V55 works, with all fixed reflections computed using a prechosen generator of the field's unit group. It yields an exact determinant-one compiler once membership in the quotient kernel is available as one ordinary query.

### V59. A semantic promise is enough for the randomized variant

If the oriented comparison tests in V55 have bounded error on ordinary-positive inputs, amplify each to inverse-polynomial error below one third of the reciprocal of the total number of calls. A union bound makes the zero-bit computation correct with probability at least two thirds on the promise, and a failed ordinary query cannot turn an ordinary-NO into a YES on any tape. The compiler has one-sided error on ordinary-NO pairs and yields the one-output randomized reduction on all pairs. A separator for the randomized reduction consequently rules out the corresponding randomized oriented promise testers whenever the quotient compiler exists.

### V60. A nonuniform counterpart on fixed sign groups

With deterministic polynomial-size advice for the boundary testers of V55, hardwire the fixed number of relevant input-length advices for reflections and mode permutations, which preserve the framed size under a fixed-width encoding. The polynomial-size quotient query remains the only ordinary output other than fixed NO. Thus the advice-level strict world excludes those advice-level promise testers, independently of the uniform separation. This uses the quotient query as a gate on ordinary-NO inputs.
