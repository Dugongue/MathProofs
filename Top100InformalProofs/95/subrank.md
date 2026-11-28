# Diophantine reductions for full subrank and matrix-space containment

The fixed-format subrank assertion uses zero slices to pad to (n₀, n₀, n₀²). The diagonal-space recognition step over the rationals is randomized polynomial time. Rational undecidability requires the indicated Bertini–Brumer assumption.

## 1. Two lemmas

**Lemma 1 (full subrank = rank-one frame).** Let T ∈ Kⁿ⊗Kⁿ⊗K^m have slices T_1, …, T_m ∈ M_n(K), and put L = span(T_k). Then Q_K(T) ≥ n iff L contains n rank-one matrices u_t v_tᵀ (t = 1..n) such that {u_t} and {v_t} are each bases of Kⁿ. Always Q_K(T) ≤ n.

*Proof.* Q(T) ≤ n because ⟨r⟩ ≤ T forces the first flattening rank ≥ r. (⇒) Let (A⊗B⊗C)T = ⟨n⟩ with A, B ∈ M_n(K), C ∈ K^{n×m}. The third-factor slices of the output are M'_t := Σ_k C_tk A T_k Bᵀ = E_tt. Put M_t = Σ_k C_tk T_k ∈ L. Summing, A(Σ_t M_t)Bᵀ = I, so A, B are invertible and M_t = A⁻¹E_ttB⁻ᵀ = u_t v_tᵀ, u_t = A⁻¹e_t, v_t = B⁻¹e_t. (⇐) Let A = [u_1…u_n]⁻¹, B = [v_1…v_n]⁻¹ and let row t of C express u_t v_tᵀ in the slices. Then the output slices are A u_t v_tᵀ Bᵀ = E_tt. ∎

**Lemma 2 (rank-one locus gadget, any field).** Let G_1, …, G_e ∈ K[x_1..x_n] be quadratic forms and N_k ∈ M_n(K) any matrices with xᵀN_k x = G_k(x) (upper triangular works in every characteristic). Let L ⊆ M_n(K) be the orthogonal complement, under ⟨X,Y⟩ = tr(XᵀY), of span{E_ij − E_ji (i<j), N_1, …, N_e}. Then the rank-one matrices in L are exactly λxxᵀ with λ ≠ 0 and x ≠ 0, G_k(x) = 0 for all k.

*Proof.* ⟨uvᵀ, E_ij − E_ji⟩ = u_iv_j − u_jv_i, so uvᵀ ⊥ all alternating E_ij − E_ji iff u ∥ v. With v = λu, ⟨uvᵀ, N_k⟩ = λuᵀN_ku = λG_k(u). ∎

So FULLSUB on such L asks whether the projective variety X = {G_k = 0} has n rational points spanning Kⁿ.

## 2. Theorem A

**Theorem A.** For every field K, FULLSUB_K ≡_p HTP(K), where HTP(K) is solvability over K of finite systems of polynomial equations with coefficients in K (rational coefficients when K = ℚ).

*Membership.* Q_K(T) ≥ n is "∃ A, B, C over K with (A⊗B⊗C)T = ⟨n⟩", a polynomial system over K.

*Hardness (the spanning-points trick).* Reduce from quadratic systems (every system is equivalent to a quadratic one by naming products). Let

  f_i(z) = Σ_{j<k} a_ijk z_j z_k + Σ_j a_ijj z_j² + Σ_j b_ij z_j + c_i,  i = 1..s, z ∈ K^d.

Use n = 2d+1 coordinates x = (x₀, z_1..z_d, z'_1..z'_d) and the homogeneous quadratic forms

  G_i = Σ_{j<k} a_ijk z_j z_k + Σ_j a_ijj z_j z'_j + x₀ Σ_j b_ij z_j + c_i x₀²,
  H_j = x₀ (z_j − z'_j).

No G_i or H_j contains a square z_j² or z'_j². Let X = {G_i = H_j = 0} ⊆ P^{2d} and build L by Lemma 2, T with slices a basis of L (polynomial time: one kernel computation).

- Every coordinate point e_{z_j}, e_{z'_j} lies on X: each monomial of each form has a factor x₀ or two distinct variables. These 2d points span the hyperplane {x₀ = 0}.
- A point of X with x₀ ≠ 0, scaled to x₀ = 1, has z' = z (from H_j) and then G_i(1, z, z) = f_i(z) = 0. Conversely, a solution z gives the point (1, z, z) ∈ X.

So X(K) spans K^n iff it contains a point off {x₀ = 0} iff f has a K-solution, and then {e_{z_j}, e_{z'_j}, (1, z, z)} is a basis. By Lemmas 1 and 2 (u_t = x_t, v_t = λ_t x_t), Q_K(T) = n iff f is solvable over K. In characteristic ≠ 2 one may take N_k symmetric, so L ⊆ Sym_n and T has symmetric slices. ∎

**K3 check.** `subrank_gadget.cpp` builds T_f for f = (z₁z₂ − 1, z₁ + z₂ − 5/2, z₁² − 4), with n = 5 and m = 10. It verifies in exact rational arithmetic that the five spanning points lie on X, that each xxᵀ lies in L, and that (A⊗A⊗C)T_f = ⟨5⟩. Output: 0 violations in each check. The unsolvable direction is the proof above, not computation.

**Corollary A1.**
1. Over ℚ, with [BB], FULLSUB_ℚ is Σ⁰₁-complete, so n ↦ [Q_ℚ(T) ≥ n] is not computable.
2. Over ℚ̄ and ℝ it is decidable (Tarski / quantifier elimination). Over F_q it is NP-complete; the reduction above is polynomial, and quadratic systems over F_q are NP-complete.
3. Over a number field K, FULLSUB_K ≡ HTP(K): Σ⁰₁-complete for K = ℚ, open otherwise.
4. Contrast with r6 Thm E: the asymptotic subrank of a ℚ-tensor equals that over ℂ. So subrank is undecidable, asymptotic subrank is field-blind, and the arithmetic sits entirely in the non-asymptotic preorder.

**Corollary A2 (matrix-space containment vs isomorphism).** "Given L ⊆ M_n(ℚ), is P·D_n·R ⊆ L for some invertible P, R?" (D_n = diagonal matrices) is FULLSUB in other words: Lemma 1 says that L contains n rank-one matrices with independent rows and independent columns. So it is Σ⁰₁-complete. "Is L = P·D_n·R?" is an orbit question, decidable (it is randomized polynomial time: first find an invertible element using randomized determinant identity testing: L must be an n-dimensional space with n independent rational rank-one elements, which one finds by simultaneous diagonalisation of the commutative algebra L·L₀⁻¹ for an invertible L₀ ∈ L).

**Corollary A3 (fixed format).** Suppose quadratic HTP(ℚ) is undecidable with d₀ unknowns. This follows from [BB] + Matiyasevich bounded-unknown universality + degree reduction (audit-B3B4 F2); d₀ is not numerically evaluated. Then the number of independent quadratic equations is ≤ C(d₀+2,2), and Theorem A gives a single format (2d₀+1, 2d₀+1, m₀), with L padded to a fixed dimension, on which full subrank over ℚ is undecidable. Compare ledger 11-24 l.290: tensor rank was the listed exception to fixed-size undecidability; subrank is not an exception.

## 3. Theorem B: fixed small targets

CONTAIN_D: given L ⊆ M_{n×n'}(ℚ), decide whether some P (n×k, injective) and R (l×n', surjective) give P·D·R ⊆ L, for a fixed D ⊆ M_{k×l}(ℚ).

**Lemma 3 (RANK1).** RANK1_K, "does L ⊆ M_n(K) contain a rank-one matrix?", is ≡_m HTP(K) for every number field K.
*Proof.*
- Upper bound: x ≠ 0 ⟺ ∃y Σx_iy_i = 1.
- Lower bound: [PHTP] gives HTP(K) ≡ nontrivial zeros of a form F.
  - Replace F by F² (even degree 2D, same zeros) and write F² = Q(v_D(x)) as a quadratic form in the degree-D monomials.
  - The Veronese image v_D(P^n) is cut out by quadrics, and its K-points are the images of K-points (coordinate ratios are ratios of monomials).
  - Lemma 2 applied to the system {Veronese quadrics, Q} finishes. ∎

**Theorem B.** For D ∈ {⟨E₁₁⟩, ⟨I_k⟩ (any fixed k ≥ 1), D_k (any fixed k ≥ 1)}, CONTAIN_D ≡_m HTP(ℚ). With [BB] each is Σ⁰₁-complete.

*Proof.* Upper bound: existential over ℚ. Lower bounds come from RANK1_ℚ.
- **⟨E₁₁⟩.** This is RANK1.
- **⟨I_k⟩.** Map L ↦ L ⊗ I_k (Kronecker). Then rank(M ⊗ I_k) = k·rank M, so L⊗I_k contains a matrix of rank exactly k iff L contains rank one. A copy of ⟨I_k⟩ is exactly a rank-k element.
- **D_k.** Map L ↦ L^{⊕k} (block-diagonal, independent blocks).
  - The rank-one elements of L^{⊕k} sit in a single block.
  - (⇐) If uvᵀ ∈ L, placing it in each of the k blocks gives k rank-one matrices with independent column vectors and independent row vectors. Their span is P·D_k·R.
  - (⇒) A copy of D_k contains rank-one elements (the images of E_tt). One of them lies in a block, so L contains rank one. ∎

## 4. Proposition C: twisted targets carry their own field

Let K be a number field, [K:ℚ] = d, and D_K ⊆ M_d(ℚ) the regular representation of K (D_ℚ = ⟨E₁₁⟩).

**Proposition C.** HTP(K) ≤_m CONTAIN_{D_K} ≤_m HTP(ℚ).

*Proof.*
- Upper bound: existential over ℚ.
- Lower bound: reduce RANK1_K (≡ HTP(K) by Lemma 3) via L₀ ↦ Res(L₀) ⊆ M_{dn}(ℚ), the realification of the K-space L₀ ⊆ M_n(K).
  - (⇐) If ww'ᵀ ∈ L₀ has rank one, then Res(K·ww'ᵀ) = Res(w)·D_K·Res(w'ᵀ), with Res(w) injective and Res(w'ᵀ) surjective.
  - (⇒) Res(L₀) ⊗_ℚ K̃ (K̃ the Galois closure) is {(M_σ)_σ : …}, block-diagonal over the d embeddings σ, with the σ-block equal to σ(L₀). This is because Res(L₀) commutes with the K-structure, which diagonalises over K̃.
  - A copy P·D_K·R ⊗ K̃ contains rank-one elements: the images of the primitive idempotents of K⊗K̃ ≅ K̃^d, rank preserved by P injective and R surjective.
  - A rank-one block-diagonal element lives in one block σ(L₀), so σ(L₀) and hence L₀ contains a rank-one K-matrix (apply σ⁻¹ to a K̃-point and descend). The descent needs care: the rank-one element is defined over K̃, not K. **Fix:** the K̃-point of the rank-one locus of σ(L₀) given by the idempotent image e_σ is Gal(K̃/σK)-stable up to scaling, since the copy is defined over ℚ and the idempotent e_σ is fixed by Gal(K̃/σK). So the line is σK-rational, and σ⁻¹ gives a K-rational rank-one element of L₀. ∎

*Comments.*
- For K = ℚ(i): HTP(ℚ(i)) ≤ CONTAIN_{D_{ℚ(i)}} ≤ HTP(ℚ). [BB] makes the right end Σ⁰₁-complete but says nothing about the left (U4: BB is ℚ-only).
- The natural upper bound CONTAIN_{D_K} ≤ HTP(K) needs the open condition "the rank-one line is not ℚ-rational up to scalar" (w ∧ w̄ ≠ 0), which uses conjugation. It holds if ℚ is Diophantine in K, which is not known.
- So a 2-dimensional fixed target, the matrix space ℚ(i) ⊆ M_2(ℚ), gives a containment problem whose decidability is **not settled by [BB]**, whereas every split fixed target is Σ⁰₁-complete (Thm B).
- With Sun 2611.25002 (unrefereed, conditional), CONTAIN_{D_K} is Σ⁰₁-complete for K = ℚ(√2), ℚ(√3), ℚ(√6).

**Conjecture C′ (containment dichotomy).** For every fixed nonzero D ⊆ M_{k×l}(ℚ), CONTAIN_D ≡ HTP(K_D) for an explicit number field K_D attached to the minimal-rank locus of D (a residue field of the étale part of the "rank-one hull" of D⊗ℚ̄). In particular CONTAIN_D is Σ⁰₁-complete iff K_D = ℚ, given [BB] and the Diophantine-ℚ-in-K hypothesis.
- Known cases: Theorem B (K_D = ℚ) and Proposition C (lower bound).
- **Not** proved in general. The naive reduction L ↦ L⊗D fails for D = ℚ(i): it finds copies inside ℚ(i)⊗ℚ(i) ≅ ℚ(i)² without any rank-one element in L.
