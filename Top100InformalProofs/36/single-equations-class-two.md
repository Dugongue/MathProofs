# Single equations and the class-two commutator map

The decision and hardness claims here concern the stated classes of torsion-free class-two groups.

## 0. Literature (checked 2026-11-22)

* Duchin, Liang, Shapiro, *Equations in nilpotent groups*, Proc. AMS 143 (2015), arXiv:1401.2471. Single equations are decidable in class-2 groups with rank-one commutator subgroup. Systems are undecidable in N_{2,r}.
* A. Levine, *Equations in virtually class 2 nilpotent groups*, Groups Complex. Cryptol. (2022), arXiv:2009.10651. Covers virtually class 2 with virtually cyclic commutator subgroup. The v1 claim for all class-2 groups was withdrawn because of Roman'kov.
* V. A. Roman'kov, J. Group Theory 19(3) (2016) 497–514. Gives class-2 groups with an undecidable commutator problem [X,Y] = g. Read via the zbMATH review only.
* Garreta–Miasnikov–Ovchinnikov, Bull. Math. Sci. 10 (2020), and Gray–Levine, arXiv:2512.07690 and 2605.30535, treat **systems**: every non-virtually-abelian f.g. nilpotent group has undecidable systems. This covers the groups of Theorem B(3) too, so single-equation decidability there is not implied by anything on systems.
* L. Lipshitz, *The Diophantine problem for addition and divisibility*, Trans. AMS 235 (1978) 271–283. The existential theory of (N, +, |) is decidable. Bel'tyukov proved the same independently (J. Soviet Math., 1980). Verified via the DOI landing page and secondary citations; we did not reread the proof.
* In-house: r1 `free-nilpotent.md` and its audit (SE(N_{2,r}) decidable for all r, Theorem 5), and r1 `nilpotent-equations.md` (frame proof of Roman'kov, one-variable decidability, Proposition 3 on products).
* **Novelty search.** Web searches turned up no single-equation result for abelian-by-cyclic class-2 groups with non-cyclic commutator subgroup (for example the "Heisenberg group over Z^k"), and no use of Lipshitz's theorem for group equations. This was a light search; the Russian-language literature (Roman'kov's school) was not checked.

---

## 1. Theorem A: the dictionary

**Setup.** Let G be f.g., torsion-free, of class ≤ 2.

* Z := Z(G) ≅ Z^m.
* Γ := G/Z is torsion-free: if x^k ∈ Z then [x,y]^k = [x^k,y] = 1, so [x,y] = 1 for all y and x ∈ Z. So Γ ≅ Z^n.
* The commutator map induces an alternating bilinear map ω : Γ × Γ → Z, equivalently a linear map ω̃ : Λ²Γ → Z. It is nondegenerate: its radical is trivial, by the definition of Z.

**Lemma 1.1 (normal form of the group).** Fix a basis e_1..e_n of Γ, lifts s_i ∈ G, and put σ(x) = s_1^{x_1} ⋯ s_n^{x_n}.

* Collecting gives σ(x)σ(y) = σ(x+y) · τ(x,y), with τ(x,y) = Σ_{i>j} x_i y_j [s_i,s_j]^{±1}. The sign is fixed by the convention; τ is bilinear and Z-valued.
* Hence G ≅ G_ω := Γ × Z with product (x,c)(y,d) = (x+y, c+d+τ(x,y)), and [(x,c),(y,d)] = ±ω(x,y).
* G_ω depends only on ω up to isomorphism. This follows from H²(Z^n; Z^m) ≅ Hom(Λ²Z^n, Z^m) (universal coefficients) and is not needed below. ∎

Let L := ω̃(Λ²Γ) ⊆ Z, which has finite index in the isolator of [G,G]. Let K := ker ω̃, a saturated sublattice of Λ²Γ because Z is torsion-free. Then Λ²Γ/K ≅ L.

**Lemma 1.2 (equation normal form; generalises r1 Lemmas 2.1–2.2).** Let w(X_1..X_k) be a word with constants, and let e_i be the exponent sums.

(a) **If e ≠ 0, then w = 1 is decidable.** Write X_i = (x_i, c_i) in G_ω. The equation reads Σ e_i x_i = −a_0 in Γ, together with Σ e_i c_i + Q(x) = 0 in Z, where Q is an integral polynomial map. The c_i are free, so this holds iff Q(x) ≡ 0 mod gZ for g = gcd(e_i). That depends only on x mod g. Enumerate residues and solve the linear system by Smith normal form.

(b) **If e = 0,** move the constants to the right. In class 2, g X^ε = X^ε g [g,X^ε] and [g,X^{-1}] = [g^{-1},X], so

  w = w_X · g_0 · ∏_i [h_i, X_i],

where w_X lies in the derived subgroup of the free class-2 group. Hence w_X = ∏_{i<j}[X_i,X_j]^{a_ij}. Every factor other than g_0 lies in [G,G] ⊆ Z. So w = 1 is solvable iff g_0^{-1} =: c_0 ∈ L and there are x_i ∈ Γ with

  Σ_{i<j} a_ij ω(x_i,x_j) + Σ_i ω(h̄_i, x_i) = c_0.        (QE)

The central coordinates of the X_i do not occur. ∎

**Theorem A.** SE(G) is computably equivalent to SE(N_{2,n}/K), where N_{2,n}/K = Z^n × (Λ²Z^n/K) with the induced cocycle. The equivalence is uniform in G. It depends only on the pair (n, K) up to the action of GL_n(Z) on Λ²Z^n. In particular, decidability of single equations is an isomorphism invariant of G and an invariant of the integral TI-orbit of the commutator tensor.

*Proof.* In both groups the e ≠ 0 equations are decidable by Lemma 1.2(a). For e = 0, (QE) in G asks whether c_0 ∈ L and whether Σ a_ij x_i∧x_j + Σ h̄_i∧x_i ∈ ω̃^{-1}(c_0) = c̃ + K for any preimage c̃ ∈ Λ²Z^n. Membership c_0 ∈ L and the preimage c̃ are computable by linear algebra. The same membership problem, with the same K, is (QE) in N_{2,n}/K, and conversely: target classes in Λ²Z^n/K map bijectively onto L. A change of basis of Γ acts on K by Λ²g. ∎

From here on, "the group (n, K)" means N_{2,n}/K with K saturated and ω nondegenerate. The landmarks:

* free N_{2,n}: K = 0;
* DLS groups: rk K = C(n,2) − 1;
* direct products: K_1 ⊕ K_2 ⊕ (Z^{n_1} ⊗ Z^{n_2}).

**Remark (the commutator sub-problem is Plücker geometry).** With t = 1 and no constants, (QE) asks whether the affine lattice coset c̃ + K meets the cone of integral decomposable bivectors. Every integral bivector of rank ≤ 2 is x∧y with x, y integral (r1 §3). So the commutator problem is "integral points on the affine cone over Gr(2,n) intersected with an affine subspace". Single equations with t pairs replace the cone by its t-th secant variety, with congruence conditions and a linear defect S∧Z^n added (r1 Lemma 2.3 and the completion of products).

---

## 2. Theorem B: decidable side

**B1 (K = 0).** This is r1 Theorem 5: SE(N_{2,n}) is decidable, audited PASS. By Theorem A it covers every G in which ω̃ is injective. Examples are N_{2,n} × Z^s and any finite-index-centre variant.

**B2 (rk L = 1).** Duchin–Liang–Shapiro, Thm 3.

**B4 (orthogonal sums).** By r1 Proposition 3, an equation over G_1 × G_2 is solvable iff both coordinate projections are. Each G_i is a retract, so an equation over G_i embeds. Hence SE(G_1 × G_2) is decidable iff SE(G_1) and SE(G_2) are. In tensor terms, the decidable class is closed under orthogonal sum ω_1 ⊥ ω_2 and under taking orthogonal summands.

### B3. Isotropic hyperplanes (new)

**Definition.** A hyperplane V ⊂ Γ (a saturated subgroup of corank 1) is *ω-isotropic* if ω(V,V) = 0.

**Lemma 2.1 (three equivalent conditions).** For G torsion-free, class 2 and non-abelian, the following are equivalent:

(i) Γ has an ω-isotropic hyperplane;

(ii) G is abelian-by-cyclic: it has an abelian normal subgroup A with G/A cyclic;

(iii) the alternating matrix space spanned by the coordinate forms of ω has the shape {e₀*∧φ : φ ∈ W} for one fixed e₀* ∈ Γ*_Q.

*Proof.* (i)⇒(ii): take A = preimage of V. It is abelian since [V,V] = ω(V,V) = 0, normal since it contains [G,G], and G/A ≅ Γ/V ≅ Z.

(ii)⇒(i): the image Ā of A in Γ is isotropic, and Γ/Ā is cyclic. If Γ/Ā were finite, Ā would have finite index, so ω_Q = 0 and G would be abelian. So Γ/Ā ≅ Z, which is torsion-free, and Ā is a saturated hyperplane.

(i)⇔(iii): choose e_0 with Γ = Ze_0 ⊕ V. If V is isotropic, then for every coordinate functional λ on Z,

  λ∘ω(x,y) = x_0 λπ(y_V) − y_0 λπ(x_V),  with π(v) := ω(e_0, v).

That is, λ∘ω = e₀*∧(λ∘π). Conversely, if every form is e₀*∧φ, then V := ker e₀* ∩ Γ is isotropic. ∎

**Theorem B3.** If Γ has an ω-isotropic hyperplane, SE(G) is decidable.

*Proof.* By Lemma 1.2 it suffices to decide (QE). Write Γ = Ze_0 ⊕ V and π(v) = ω(e_0,v) as above, so that

  ω(ξe_0 + v, ξ'e_0 + v') = π(ξv' − ξ'v).

Put x_i = ξ_i e_0 + v_i and h̄_i = η_i e_0 + h_i' with ξ_i, η_i ∈ Z and v_i, h_i' ∈ V. Let A be the alternating integer matrix with A_ij = a_ij for i < j. Expanding (QE):

  π( Σ_j λ_j(ξ) v_j ) = c_0 + π( Σ_i ξ_i h_i' ),

where λ_j(ξ) := (A^T ξ)_j + η_j is affine-linear in ξ ∈ Z^k.

* For fixed ξ, the left side ranges exactly over π(g(ξ)V), where g(ξ) := gcd_j λ_j(ξ), with g = 0 if all λ_j vanish. This is because the v_j are free in V.
* c_0 must lie in L = π(V). If it does not, there is no solution; this is decidable. Pick c̃ ∈ V with π(c̃) = c_0.
* Let N := ker π, saturated in V, and choose a splitting V = N ⊕ V' with coordinate functionals ρ_1..ρ_s on V' (s = rk L). Then gV + N = N ⊕ gV'.

So (QE) is solvable iff

  ∃ ξ ∈ Z^k :  for every r ≤ s,  ρ_r(R(ξ)) ∈ λ_1(ξ)Z + … + λ_k(ξ)Z,  where R(ξ) := c̃ + Σ_i ξ_i h_i'.       (★)

All of ρ_r(R(ξ)) and λ_j(ξ) are affine-linear integer forms in ξ.

**CRT linearisation.** For integers y, ℓ_1..ℓ_k:

  y ∈ Σ_j ℓ_j Z  ⟺  ∃ z_1..z_{k−1} :  ℓ_1 | z_1 ∧ … ∧ ℓ_{k−1} | z_{k−1} ∧ ℓ_k | (y − z_1 − … − z_{k−1}).

Here a | b means ∃q : b = aq, so 0 | b ⟺ b = 0. This convention also handles the case where every ℓ_j is 0.

* (⇐) is immediate.
* (⇒) If y = Σ q_j ℓ_j, take z_j = q_j ℓ_j.

So (★) is an existential sentence in ⟨Z; +, |, 0, 1⟩ with atoms ℓ | ℓ' for affine-linear terms ℓ, ℓ'. It translates to finitely many existential sentences over ⟨N; +, |⟩: write each integer variable as p − q with p, q ∈ N, and split each atom ℓ | ℓ' on the signs of ℓ and ℓ' (with |ℓ| = A − B or B − A for N-terms A, B). Lipshitz (1978) decides these. ∎

**Remarks.**

* The proof decides the quadratic system only because, once the scalar coordinates ξ are fixed, the V-coordinates enter linearly with **scalar** coefficients times a fixed map π. That is what isotropy of a hyperplane buys.
* Already for an isotropic subspace of corank 2 the coefficient lattice becomes Σ_j Im(λ_j π_1 + μ_j π_2). Membership there involves the determinantal divisors of a pencil, which are binary forms of degree up to rk L. The divisibility language no longer suffices.
* The B3 class contains groups with rank L anywhere from 1 to n − 1, for example π : Z^{n−1} → Z^{n−1} the identity, giving the "Heisenberg group over Z^{n−1}" ((Z^{n−1})² ⋊ Z). For n−1 ≥ 2 these are covered neither by DLS/Levine (commutator subgroup Z^{n−1}, not virtually cyclic) nor by r1.

**Corollary B5 (small rank).** If h(G/Z(G)) ≤ 3, SE(G) is decidable.

*Proof.* n ∈ {0, 2, 3}; n = 1 is impossible for a nondegenerate ω.

* n = 2: rk L = 1, so B2 applies.
* n = 3: Λ²Q³ ≅ Q³. If rk L = 3, then K = 0 and B1 applies. If rk L = 1, B2 applies. If rk L = 2, the dual space of forms is 2-dimensional inside Λ²(Q³)* ≅ Q³. Two forms of rank 2 on Q³ correspond to two planes, which meet in a line ⟨e₀*⟩, and both forms are divisible by e₀*. So Lemma 2.1(iii) holds and B3 applies. ∎

**Remark (n = 4).** n = 4 is therefore the first case with open instances. There Λ²Z⁴ ≅ Z⁶ and rk K ∈ {1, …, 4} needs a new idea when no isotropic hyperplane exists and no orthogonal splitting exists. The simplest open groups are rk K = 1, with K spanned by:

* a decomposable bivector e_1∧e_2, giving N_{2,4} with one commutator killed; or
* a nondegenerate bivector e_1∧e_2 + d e_3∧e_4.

A plausible route in both cases is to rerun the r1 §7 strong-approximation argument with the target allowed to move in the line c̃ + K. That argument needs the target fixed; this is the first concrete test of whether it extends.

---

## 3. Theorem C: undecidable side as a matrix-space invariant

Let U, V be free abelian of ranks a, b, let Γ = U ⊕ V, and use Λ²Γ = Λ²U ⊕ Λ²V ⊕ (U⊗V). For a saturated sublattice K ⊆ U⊗V (a "matrix space" of a×b integer matrices), put G_K := N_2(U⊕V)/K. In this group:

* U and V each generate a free class-2 group;
* the coupling between them is U⊗V/K, i.e. the bilinear map B_K : U × V → (U⊗V)/K.

**Rank-one coset problem R(K).** Given γ ∈ U⊗V, decide whether γ + K contains an integral matrix of rank ≤ 1, i.e. a matrix u v^T with u ∈ U, v ∈ V. R(K) is invariant under GL(U) × GL(V) acting on K, so it is a matrix-space (3-tensor) isomorphism invariant in the Grochow–Qiao sense.

**Theorem C.** For every K, R(K) ≤_m SE(G_K). More precisely, for γ ∈ U⊗V the equation [X,Y] = γ̄, where γ̄ is the central element (0,0,γ mod K), is solvable iff γ ∈ R(K).

*Proof.* In G_K, [(u,v,·),(u',v',·)] = (u∧u', v∧v', u⊗v' − u'⊗v mod K).

* (⇐) If u⊗v ≡ γ, take X = (u,0), Y = (0,v).
* (⇒) Suppose u∧u' = 0 and v∧v' = 0.
  * The Sublemma of r1 Theorem 1 gives u = λw, u' = μw, v = αt, v' = βt.
  * So u⊗v' − u'⊗v = (λβ − μα) w⊗t, an integral rank-≤1 matrix congruent to γ mod K.
  * If a = 1 or b = 1 the wedge conditions are vacuous, but then every matrix has rank ≤ 1 and both sides are trivially true. ∎

**Corollary C1 (explicit undecidable family).** Let D be an r.e.-complete Diophantine set and let B : Z^{n+1} × Z^{n+1} → Z^M be the frame map of r1 Lemma 1. Let K_D := ker(B̃ : U⊗V → Z^M), which is saturated. Then R(K_D) is undecidable, so SE(G_{K_D}) is undecidable.

*Proof.* p ∈ D ⟺ c(p) ∈ B(Z^{n+1}, Z^{n+1}) (r1 Lemma 1) ⟺ c(p) ∈ B̃(U⊗V) and γ_p ∈ R(K_D), for any computable preimage γ_p. The first condition is a decidable lattice test. ∎

This is exactly the r1 group G_D, up to the inessential non-saturation of B̃'s image. It re-proves Roman'kov's theorem in tensor language. The invariant that controls this side is the arithmetic of integral points on the linear section (γ + K) ∩ Seg(U × V) of the Segre cone. Undecidability arises once that section can carry a linearised Diophantine system, as the frame does: u_0 v_0 = 1 forces u = v = (1,x), and the remaining linear conditions on the matrix entries T_ij = x_i x_j encode the monomial relations x_k = x_i x_j.

**What C does not give.**

* (b) asked for a family characterised by a *transversality* or *codimension* invariant. The frame family is characterised only by "R(K) encodes a universal Diophantine set". We found no codimension or genericity criterion that implies undecidability, and Theorem B shows that none can be purely dimensional: B3 groups exist at every intermediate codimension of the form C(n,2) − (n−1).
* All known undecidable examples have a large rank: n = 2(N+1), with N in the thousands for a universal polynomial. They also lie in an **overdetermined** regime, where rk L far exceeds 2n − 3 = dim of the decomposable cone. By contrast, B2, B3 and the r1 nondegenerate stratum are regimes where the relevant varieties are homogeneous and local–global (Siegel or strong approximation) applies.
* **Heuristic conjecture, not proved.** Undecidability needs rk L > 2n − 3 or a bipartite coupling of large rank. Generic K of codimension ≤ 2n − 4 are decidable.

**Closure.** If SE(G_1) is undecidable, then SE(G_1 × H) is undecidable for every H (B4). So the set of pairs (n, rk L) carrying undecidable examples is closed under (n, ℓ) ↦ (n + r, ℓ + C(r,2)) and (n + 2, ℓ + 1).

---
