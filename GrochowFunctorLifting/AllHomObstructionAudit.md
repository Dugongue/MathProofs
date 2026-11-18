# Independent audit: all-homomorphism functor and spectrum obstructions

Verdict: the mathematical statements pass for the explicit all-covariant tensor restriction category and the source categories stated below. The published-question scope and Lie-semiring caveats are essential. No Lean or publication-priority audit is claimed.

## 1. Tensor core lemma

A d-tensor object is a tuple of finite-dimensional spaces V_i with T in their tensor product. A morphism to S is a tuple of arbitrary linear maps f_i such that their tensor product sends T to S. All modes are covariant, and d is fixed.

Let U_i(T) be the image of the i-th flattening, its minimal mode support. Under a morphism T -> S, U_i(S) is contained in f_i U_i(T), so its dimension cannot increase. If morphisms exist in both directions, all support dimensions agree. Each restricted f_i:U_i(T) -> U_i(S) is consequently an isomorphism, and these restrictions give an isomorphism of the support cores. If ambient shapes also agree, extend these support isomorphisms to the ambient spaces to obtain an isomorphism of the full tensor objects.

Thus among pairwise mutually reachable tensors of maximum mode dimension at most P, there are at most (P+1)^d isomorphism types, one for each possible ambient shape. The proof includes zero tensors: every support dimension is zero and the same shape argument applies.

## 2. Quantitative functor consequence

If a source category has a family of pairwise mutually reachable objects, every covariant or contravariant functor takes that family to one mutual-restriction class. If it reflects object isomorphism and has polynomially bounded output mode dimensions in the written source length L, the source family can have only polynomially many isomorphism types at length at most L.

This requires no faithfulness, linearity, additive preservation, full functor, or computability of the arrow map. Polynomial object dimensions and isomorphism reflection already suffice. An ordinary polynomial-time kernel reduction on object isomorphisms need not preserve arbitrary arrows, so no contradiction with known tensor-completeness reductions follows.

## 3. Explicit source families and type counts

Fix F_q and take a = floor(2n/3), b = n-a, and a fixed decomposition F_q^n = U plus W. For every bilinear map U times U -> W, extend multiplication by zero whenever an input lies in W. The algebra is associative and its third power is zero. The family contains q^{a squared times b} distinct tables, and each algebra isomorphism orbit has at most |GL_n(q)| less than q^{n squared} members. Hence there are at least q^{a squared times b - n squared} isomorphism types. Their written structure-constant length is O(n cubed) over the fixed field. All source algebras have zero homomorphisms in both directions.

Restricting multiplication to symmetric bilinear maps gives the commutative count q^{a(a+1)b/2 - n squared}. Restricting it to alternating maps gives class-at-most-two Lie algebras with count q^{a(a-1)b/2 - n squared}; Jacobi holds because the bracket image is central. These are all q^{Omega(n cubed)} families.

Unitizing the nilpotent associative or commutative algebras gives local augmented unital algebras with radical cube zero and residue field F_q. They have morphisms both ways through the augmentation to F_q and the unit inclusion. Their radicals recover the original algebras, so the superpolynomial isomorphism-type count persists. The argument also rules out a functor defined on the entire unital-algebra category, since its restriction to this family is already impossible.

The orbit count does not assume that W equals the full square or is intrinsically specified: each full GL_n orbit intersects the family in at most its full orbit size, which is all the counting argument needs. Source promises must not be changed to nondegenerate or surjective bilinear maps in this calculation.

Therefore the proposed nonexistence theorem holds for nonunital associative algebras, commutative algebras, Lie algebras, and the stated augmented local unital families, mapping to fixed-order all-covariant tensor objects with polynomial ambient dimensions and isomorphism reflection.

## 4. Spectrum obstruction

For associative algebras with all homomorphisms, the diagonal map F_q -> F_q plus F_q and either coordinate projection give morphisms in both directions, including under the unital convention. Any invariant monotone in the all-homomorphism preorder must assign these objects the same value. Direct-sum additivity and normalization at F_q require values one and two, a contradiction. Thus the proposed normalized all-homomorphism Strassen spectrum is empty.

For Lie algebras the valid statement is even independent of tensor multiplication: no direct-sum-additive invariant, monotone under all Lie homomorphisms, can be normalized to one at the one-dimensional abelian Lie algebra. Zero maps give mutual morphisms between that Lie algebra and its two-fold direct sum. This excludes any proposed compatible spectral theory with those axioms.

Do not assert that ordinary Lie algebras carry the naive tensor-product Lie semiring. The operation obtained by tensoring two brackets is generally not a Lie bracket in odd characteristic. The additive-normalization obstruction is valid without assuming such a semiring exists.

## 5. Exact relation to Grochow–Qiao Open Question 7.5

The primary SIAM paper asks which reductions can be made functorial with all homomorphisms and which relevant categories admit asymptotic spectra. Section 2.3 distinguishes object kernel reductions and their functorial behavior; Section 7.5 explicitly goes beyond isomorphism-only groupoids. Primary sources read:

- https://par.nsf.gov/servlets/purl/10494304 . The Question 7.5 excerpt was retrieved in search; direct PDF fetch timed out.
- https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full . Publisher copy verifies the problem, category context, and the object reductions.

The audited theorem gives exact negative answers for the specified reverse directions into the standard all-covariant tensor restriction category. It does not settle the entire omnibus classification of reductions and categories. It does not forbid mixed-variance intertwiner categories, tensor correspondences, isomorphism-only functors, or functors that use superpolynomial output dimensions. Dualities that identify object isomorphism problems do not automatically extend covariantly to singular maps. These scope limits should appear in the main theorem and README claim.

No mathematical counterexample to the stated all-covariant theorem was found. The only requested corrections are the category scope and the Lie-spectrum wording above.
