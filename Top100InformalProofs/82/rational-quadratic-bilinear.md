# Quadratic-bilinear equations over a number field

The classification is in the exact matrix-space model defined below. Its undecidability implications retain the underlying Diophantine assumptions.

## 1. Definitions

**Q-BLIN_F(B).** An instance is a finite system Σ_{i,j} a^{(q)}_{ij} B(u_i, v_j) = c_q, with a ∈ F, c_q ∈ W, and unknowns u_i ∈ U, v_j ∈ V. Elements are encoded in fixed bases. Multiplying an equation by a nonzero element of F (or Z) changes nothing, so integral coefficients suffice when F = Q.

**HTP variants.**
- HTP_Z(L): finite systems in Z[x], with a common zero in L.
- HTP_A(A), for a finite-dimensional commutative F-algebra A: finite systems with coefficients in A, in coordinates on a fixed basis, with a common zero in A.
- Lemma 1.1(a) of rational-problems.md gives HTP_L(L) ≡_m HTP_F(L) ≡_m HTP_Z(L) for a number field L. The proof uses a primitive element, its minimal polynomial, and an automorphism.

**Definition 1.1 (full nondegenerate quotient).**
- U_0, V_0 are the left and right radicals, Ū = U/U_0, V̄ = V/V_0.
- I_B = span B(U, V).
- B̄: Ū × V̄ → I_B.
- By manin.tex Lemma 2.4, Q-BLIN(B) and Q-BLIN(B̄) have the same solvable systems once c_q ∈ I_B. Membership c_q ∈ I_B is decidable by linear algebra; a system with some c_q ∉ I_B is a no-instance.

**Definition 1.2 (centroid).** Γ = {(X, Y, Z) ∈ End Ū × End V̄ × End I_B : B̄(Xu, v) = Z B̄(u, v) = B̄(u, Yv) for all u, v}. Operations are componentwise.

**Definition 1.3 (adjoint ring and centre).** A = {(P, Q) : B̄(Pu, v) = B̄(u, Qv)}, as in manin.tex, and C = Z(A).

**Lemma 1.4.** For nonzero B̄:
- (i) Each of the projections Γ → End Ū, Γ → End V̄ and Γ → End I_B is injective.
- (ii) Γ is commutative.
- (iii) (X, Y, Z) ↦ (X, Y) embeds Γ in C.
- (iv) Γ is a nonzero finite-dimensional F-algebra containing F.

*Proof.*
- (i) Suppose X = 0. Then B̄(u, Yv) = 0 for all u, so Yv lies in the right radical, which is 0. Then Z B̄(u, v) = 0 for all values, and the values span I_B, so Z = 0. The other two cases are symmetric. For example, if Z = 0 then B̄(Xu, v) = 0 for all v, so X = 0.
- (ii) Let γ = (X, Y, Z) and γ′ = (X′, Y′, Z′). Then B̄(XX′u, v) = B̄(X′u, Yv) = B̄(u, Y′Yv). Swapping the roles gives B̄(X′Xu, v) = B̄(u, YY′v). Also B̄(XX′u, v) = Z B̄(X′u, v) = Z B̄(u, Y′v) = B̄(Xu, Y′v) = B̄(X′Xu, v). The last step uses B̄(w, Y′v) = B̄(X′w, v). By nondegeneracy XX′ = X′X, and then (i) gives γγ′ = γ′γ.
- (iii) (X, Y) ∈ A by definition. Let (P, Q) ∈ A. Then B̄(PXu, v) = B̄(Xu, Qv) = Z B̄(u, Qv) = Z B̄(Pu, v) = B̄(XPu, v). Hence PX = XP, and symmetrically QY = YQ, so (X, Y) commutes with A.
- (iv) Γ is defined by linear equations, so it is finite-dimensional. F embeds as scalars (a, a, a), and Ū ≠ 0. ∎

**Lemma 1.5 (Γ inside C, linearly).** Let e and f be bases of Ū and V̄. Let N ⊆ Ū ⊗ V̄ be the kernel of e_i ⊗ f_j ↦ B̄(e_i, f_j), with a fixed basis ρ^{(1)}, …, ρ^{(t)}, where ρ = Σ ρ_ij e_i ⊗ f_j. For (P, Q) ∈ A the following are equivalent:
- (P, Q) is the image of an element of Γ;
- Σ_{ij} ρ^{(k)}_{ij} B̄(P e_i, f_j) = 0 for every k.

*Proof.*
- (⇒) The sum equals Z Σ ρ_ij B̄(e_i, f_j) = Z·0 = 0.
- (⇐) Define Z(Σ λ_ij B̄(e_i, f_j)) := Σ λ_ij B̄(P e_i, f_j). This is well defined because the λ in the kernel are the span of the ρ^{(k)}. Bilinear expansion gives Z B̄(u, v) = B̄(Pu, v), and B̄(Pu, v) = B̄(u, Qv) because (P, Q) ∈ A. ∎

The same lemma gives the intrinsic description Γ = {z ∈ C : (z_U ⊗ 1) N ⊆ N}.

---

## 2. Proof of the Main Theorem

Fix B and pass to B̄ (Definition 1.1). Write Γ = ∏_{i=1}^s Γ_i, with Γ_i local Artinian, maximal ideal m_i and residue field L_i = Γ_i/m_i. Let ε_i ∈ Γ be the corresponding idempotents.

**Lemma 2.1 (coefficient fields).** There is an F-algebra embedding σ_i: L_i → Γ_i with π_i ∘ σ_i = id, where π_i is the residue map.

*Proof.* L_i/F is separable (characteristic 0). Write L_i = F(θ), with minimal polynomial g, and let t ∈ Γ_i be any lift of θ. Then g(t) ∈ m_i and g′(t) is a unit. The Newton step t ↦ t − g(t)/g′(t) multiplies the m_i-adic order of g(t) by at least 2, and m_i is nilpotent. So after finitely many steps g(t) = 0, and θ ↦ t defines σ_i. ∎

### 2.1 Upper bound: Q-BLIN_F(B) ≤_m ∏_i HTP_{L_i}(L_i)

Put U_i = X_{ε_i} Ū, V_i = Y_{ε_i} V̄ and W_i = Z_{ε_i} I_B. These give direct sum decompositions.

Since B̄(X_{ε_i}u, Y_{ε_j}v) = Z_{ε_i} Z_{ε_j} B̄(u, v) = 0 for i ≠ j, we get B̄ = ⊕_i B_i with B_i: U_i × V_i → W_i.

Through σ_i, the field L_i acts on U_i, V_i and W_i (via X, Y and Z respectively). The defining identities of Γ say exactly that B_i is L_i-bilinear.

Now take an instance with all c_q ∈ I_B (otherwise output the fixed no-instance (1 = 0, …)).
- Write c_q = Σ_i Z_{ε_i} c_q, u = Σ_i u^{(i)} and v = Σ_i v^{(i)}.
- Then Σ a_{kl} B̄(u_k, v_l) = Σ_i Σ a_{kl} B_i(u^{(i)}_k, v^{(i)}_l), and the i-th summand lies in W_i.
- So the system is solvable iff, for each i, the system S_i: Σ a^{(q)}_{kl} B_i(x_k, y_l) = Z_{ε_i} c_q is solvable in U_i, V_i.

In fixed L_i-bases, S_i is a degree-2 polynomial system with coefficients in L_i (the a lie in F ⊆ L_i, the structure constants of B_i lie in L_i, and the c are in coordinates), and its unknowns are exactly the L_i-coordinates. The output is (S_1, …, S_s). All fixed data (Γ, the ε_i, σ_i, bases) depend only on B. ∎

### 2.2 Lower bound: HTP_Γ(Γ) ≤_m Q-BLIN_F(B)

This is manin.tex §§3–4 with R = F, plus Lemma 1.5.

**Rigidity over a field.** Let (a, b) be a frame, so B̄(a_i, b_j) = B̄(e_i, f_j). Steps 1–3 of manin.tex Prop. 3.3 apply verbatim and show that the a_i span Ū. Since e is a basis, the map A: e_i ↦ a_i is a surjective endomorphism of a finite-dimensional space, hence invertible. Likewise D: f_j ↦ b_j is invertible, and B̄(Au, Dv) = B̄(u, v). Step 4 is not needed. So Lemma 3.5 (named constants) holds over F.

**Gates.**
- An instance of HTP_Γ(Γ) is converted into a gate system over Γ by manin.tex Lemma 2.3.
- The gate X = γ is allowed for arbitrary γ ∈ Γ given in coordinates. Its compiled right-hand side B̄(P_γ e_i, f_j) is computed from the input. This is permitted, since c_q ranges over all of W.

**Compilation.** Use manin.tex Theorem 4.3 with these changes:
- 𝓔 is an F-basis of A.
- To equations (a)–(e) add, for each variable k and each basis relation ρ^{(t)}:
  - (f) Σ ρ^{(t)}_{ij} B̄(x_{k,i}, f_j) = 0.

Soundness:
- (a) and Lemma 3.6 give X_k ∈ A.
- (f) and Lemma 1.5 give X_k ∈ Γ.
- (b) is then automatic, but harmless.
- (c), (d) and (e) give the gates, as in manin.tex.

Completeness is as in manin.tex, since Γ ⊆ C (Lemma 1.4(iii)), and (f) holds for elements of Γ.

Finally, named constants turn the resulting extended system into a raw system, whose coefficients in F can be cleared to integers. The whole chain is computable. ∎

**Remark.** Leaving out (f) gives manin's HTP_C(C) ≤_m Q-BLIN_F(B), which is the second lower bound in §0.2.

### 2.3 Closing the sandwich: ∏_i HTP_{L_i}(L_i) ≤_m HTP_Γ(Γ)

Given (P_1, …, P_s), output the Γ-system whose polynomials are ε_i σ_i(p) for every p ∈ P_i and every i. Its variables are shared, which is harmless.

- A Γ-solution is a tuple of Γ_j-solutions. The j-th component of ε_i σ_i(p) is 0 for i ≠ j, and σ_j(p) for i = j.
- So the system is solvable iff each σ_j(P_j) is solvable over Γ_j.
- That holds iff P_j is solvable over L_j: push a solution forward with π_j, or lift one with σ_j.

Combining §§2.1–2.3 with HTP_{L}(L) ≡_m HTP_Z(L), applied coordinatewise, proves the Main Theorem. ∎

### 2.4 Product versus join

Write S_i = HTP_Z(L_i).
- **⊕ ≤_m ∏.** Map (i, P) to the tuple with P in slot i and the empty system elsewhere.
- **∏ ≤_btt ⊕.** Use s conjunctive queries.

Some special cases:
- If some L_i = Q, then ∏ ≡_m HTP(Q). For ≤, Weil-restrict each slot to Q and take the conjunction. For ≥, use slot i.
- More generally, ∏ ≤_m HTP(Q) always holds.
- Isomorphic L_i ≅ L_j merge, because conjunction over one field is a conjunction of systems.
- A many-one reduction ∏ ≤_m ⊕ for non-isomorphic, non-Q fields would need a conjunction across fields. I know no such reduction. It would follow if, for example, each L_j were Diophantine-interpretable in a common L_i.

### 2.5 Number-field coefficients and base change

All of §2 is over an arbitrary number field F.

For B over Q with solutions sought in F, use B ⊗ F. Radicals, I_B and Γ are cut out by linear equations, so they commute with field extension, and Γ(B ⊗ F) = Γ(B) ⊗ F. Hence Q-BLIN_F(B ⊗ F) ≡_m ∏ over the factors of the residue fields L_i ⊗ F.

---
