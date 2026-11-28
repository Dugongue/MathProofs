# Five symplectic tensor-isomorphism action types

The theorem has the field and action hypotheses given in the proof.

**Target.** Chen–Grochow–Qiao–Tang–Zhang, *On the complexity of isomorphism problems for tensors, groups, and polynomials III: actions by classical groups*. Journal version: *Computational Complexity*, online 2026-09-22. Line numbers below refer to the local text copy at `[local reference omitted]`.

- **Line 218.** "Our main results are for the real orthogonal groups and complex unitary groups; we discuss some difficulties encountered with symplectic groups in Section 1.5 and leave open the questions for more general bilinear-form-preserving groups."
- **Line 397.** "…the reductions between the five actions on 3-way arrays seem not to work for symplectic. One stumbling block (pun intended) in the symplectic case is that even a symplectic block-diagonal matrix … need not have its individual blocks be symplectic."
- **Zhili Chen's UTS thesis** (`[local reference omitted]`, line 795) says the same: "we still haven't found any solutions for the symplectic group case."

This is a stated open item in the paper, not a numbered Question. Question 7.5 (line 1634) asks about other form-preserving groups, such as O(p, q) and forms that are neither symmetric nor skew. Corollary 3 below partly answers it.

**Result (informal, 2026-11-10).** Over every field, the five isomorphism problems of CGQTZ Definition 1.7 for the symplectic family Sp are TI-complete, and hence pairwise polynomial-time equivalent. The same holds for every family of form-preserving groups with polynomially large hyperbolic blocks. Examples are standard-form O over any field of characteristic ≠ 2 in which −1 is a sum of two squares, and real O(p, q) with min(p, q) ≥ n^ε.

**How it is proved.** The theorem is a short corollary of three facts:
1. CGQTZ Theorem 1.10: each G-action reduces to TI, over any field (lines 215 and 624).
2. Grochow–Qiao (arXiv:1907.00309) Theorem A: TI reduces to each of the four other GL-actions, over arbitrary fields. This is at line 154 of the local copy in `[local reference omitted]`. Their abstract says "all but one" of the reductions work over arbitrary fields; the exception is the cubic-form reduction, which is not used here.
3. The hyperbolic padding that gives TI ⊆ TI_Sp, from our [research manuscript] (Lean: `ti_eq_tisp`, 2026-09-15).

The new parts are Lemma 1 (the collapse from five problems to three) and Lemma 2 (padding for actions where modes share a transporter). Both are elementary, and experts may regard the whole theorem as routine once stated. The point is that the case CGQTZ leave open is settled.

## Setting

Let F be a field. Let G = {G_n} be a family of groups, where G_n ≤ GL(n, F) preserves a nondegenerate bilinear form Ω_n:

G_n = { P : PᵀΩ_nP = Ω_n }.

Assume n ↦ Ω_n is computable in polynomial time; this is the CGQTZ hypothesis for Theorem 1.10. Some families, such as Sp, exist only in some dimensions; instances in other dimensions are excluded. The five G-problems are those of Definition 1.7, with every GL factor replaced by the corresponding G_n. Write (i)_G, …, (v)_G for them, and (i)_GL, …, (v)_GL for the GL versions.

## Lemma 1: five actions collapse to three for every form-preserving group

If PᵀΩP = Ω, then ΩP = P^{−t}Ω, so

P^{−t} = ΩPΩ^{−1}.

**(iii)_G ≡ (ii)_G.** Send A ∈ T(l×l×m) to Â := (I, Ω_l^{−1}, I)·A. This map is a bijection and preserves size. For P ∈ G_l and Q ∈ G_m:

(P, P, Q)·Â = (P, PΩ^{−1}, Q)·A = (I, Ω^{−1}, I)·(P, ΩPΩ^{−1}, Q)·A = (I, Ω^{−1}, I)·(P, P^{−t}, Q)·A.

So B = (P, P^{−t}, Q)·A if and only if B̂ = (P, P, Q)·Â. The same map, run backwards via A = (I, Ω, I)·Â, gives the reverse reduction.

**(iv)_G ≡ (v)_G.** The same argument works with Â := (I, I, Ω_l^{−1})·A.

Both reductions keep every side length unchanged. When Ω is a signed permutation matrix (as for Sp, and for standard O), they use only the constants 0 and ±1.

CGQTZ observe this collapse only for O(n, ℝ), where Ω = I (line 121). It holds for every form-preserving family.

## Lemma 2: padding with a hyperbolic block

**Hyperbolic hypothesis (H).** There is a polynomial-time map l ↦ (n(l), C_l) with n(l) ≤ poly(l), C_l ∈ GL(n(l), F), and nonzero scalars α, β, such that

C_lᵀ Ω_{n(l)} C_l = diag( [[0, αI_l], [βI_l, 0]], R_l ).

In the new basis, F^{n(l)} = U ⊕ U′ ⊕ R. Here U and U′ are l-dimensional, totally isotropic, and paired with each other, and R is the Ω-orthogonal complement on both sides.

**The lift.** For g ∈ GL(U), put

λ(g) := C_l · diag(g, g^{−t}, I_R) · C_l^{−1}.

Then λ(g) ∈ G_{n(l)}, because the middle factor preserves the block form:

diag(g, g^{−t}, I)ᵀ · diag([[0, αI],[βI, 0]], R) · diag(g, g^{−t}, I) = diag([[0, α gᵀg^{−t}],[β g^{−1}g, 0]], R) = diag([[0, αI],[βI, 0]], R).

**Concise spaces.** For a tensor T, write C_i(T) for its mode-i concise space, the column space of the mode-i flattening. For invertible h, C_i(h·T) = h_i C_i(T).

**Lemma 2.** Assume (H). For each X ∈ {(i), …, (v)}, X_GL reduces to X_G in polynomial time, with side lengths n(l).

*Construction.* Embed an X_GL-instance (A, B) into the X_G-instance (Ã, B̃): put A in the U-coordinates of each mode, using block U_l for a mode of size l, and then change basis by C in each mode.

*Forward.* If B = g·A for a GL-transporter g, then the λ-lift of g is a G-transporter from Ã to B̃. In the shared modes the lift is the same λ(g) every time, so it has the required form.

*Backward, independent modes, action (i).* Let h·Ã = B̃ with h_i ∈ G. Remove the basis change C. Then h_i maps C_i(Ã) ⊆ U_i onto C_i(B̃) ⊆ U_i. The restriction h_i|_{C_i(Ã)} is an injective linear map into U_i, so it extends to some g_i ∈ GL(U_i). Since Ã is supported on C₁(Ã) ⊗ C₂(Ã) ⊗ C₃(Ã), we get g·A = h·Ã = B̃, which is B.

*Backward, shared modes, actions (ii) and (v).* This is the step not covered by the earlier padding argument.
- Action (ii) uses (P′, P′, Q′). Put S_A := C₁(Ã) + C₂(Ã) ⊆ U and S_B := C₁(B̃) + C₂(B̃) ⊆ U. Then P′ maps C₁(Ã) onto C₁(B̃) and C₂(Ã) onto C₂(B̃). By linearity P′(S_A) = S_B ⊆ U.
- Extend P′|_{S_A} to g ∈ GL(U), and extend Q′|_{C₃(Ã)} to h ∈ GL(W) as before. Then g agrees with P′ on C₁(Ã) and on C₂(Ã), and Ã is supported on C₁ ⊗ C₂ ⊗ C₃. So (g, g, h)·A = (P′, P′, Q′)·Ã = B.
- Action (v) is the same with S_A := C₁ + C₂ + C₃.

*Actions (iii) and (iv).* No direct padding is needed. The Theorem only uses TI ≤ X_G, and for these two that comes from TI ≤ (ii)_GL ≤ (ii)_G ≡ (iii)_G and TI ≤ (v)_GL ≤ (v)_G ≡ (iv)_G, with the last step by Lemma 1.

*Size.* The side length goes from l to n(l). It is linear whenever n(l) = O(l), as for Sp and for O over the fields in Corollary 2. ∎

## Theorem

Let G preserve a polynomial-time-constructible family of nondegenerate bilinear forms and satisfy (H). Then each of the five G-problems is TI-complete. In particular they are pairwise polynomial-time equivalent.

*Proof.*
- **Membership.** Each X_G reduces to TI by CGQTZ Theorem 1.10.
- **Hardness.** TI reduces to X_GL for each X by GQ Theorem A, over arbitrary fields. Then X_GL reduces to X_G by Lemma 2.
- **Equivalence.** For any X and Y, compose: X_G ≤ TI ≤ Y_GL ≤ Y_G. ∎

## Corollaries

**Corollary 1 (Sp, every field, including characteristic 2).** CGQTZ fix the form at line 446, (u, v) = Σ_{i≤n}(u_i v_{2n−i+1} − u_{n+i} v_{n−i+1}). Its matrix is Ω = [[0, K], [−K, 0]], where K is the n×n anti-identity.
- The form is alternating in every characteristic. In ω(u, u) the two sums agree after the substitution i ↦ n − i + 1, so they cancel.
- Hypothesis (H) holds with C = I, α = 1, β = −1, and the second block written in the K-reversed basis. Concretely, λ(g) = diag(g, K g^{−t} K), and diag(g, Kg^{−t}K)ᵀ Ω diag(g, Kg^{−t}K) = [[0, gᵀKKg^{−t}K], [−Kg^{−1}KKg, 0]] = Ω.
- n(l) = 2l, so the GL → Sp direction is linear-length.

So the five Sp-problems are TI-complete and pairwise polynomial-time equivalent over every field. This settles the case CGQTZ leave open at lines 218 and 397. Their worry was that block-diagonal symplectic matrices need not have symplectic blocks; the concise-space argument never needs the blocks to be symplectic.

**Corollary 2 (standard-form O, char F ≠ 2, −1 = a² + b² in F).** Examples: ℂ, every finite field of odd characteristic, ℚ_p for odd p, and ℚ(i). Fix a, b ∈ F with a² + b² = −1; for a fixed field these are hard-wired constants. In F⁴ with Ω = I, take
- L = span{(1, 0, a, b), (0, 1, b, −a)},
- L′ = span{(1, 0, −a, −b), (0, 1, −b, a)}.

Both are totally isotropic: each vector has norm 1 + a² + b² = 0, and the cross terms ab − ab vanish. The L × L′ Gram matrix is 2I₂, since 1 − a² − b² = 2 and the cross terms are 0. So the Gram matrix in the basis (L, L′) is 2·[[0, I₂], [I₂, 0]].

Taking direct sums gives (H) in dimensions n = 4⌈l/2⌉, with α = β = 2 and R = 0. Hence, over such F, the five standard-form orthogonal problems are TI-complete and pairwise equivalent. In particular TI_{O(·,ℂ)} = TI for the complex orthogonal group.

**Corollary 3 (O(p, q) over ℝ; partial answer to Question 7.5).** ⟨1, −1⟩ is a hyperbolic plane with basis e₁ + e₂, e₁ − e₂ (norms 0, pairing 2). Let the family O(p_n, q_n) be polynomial-time-constructible with min(p_n, q_n) ≥ n^ε. Then (H) holds with n(l) ≤ l^{1/ε}, and the five O(p, q)-problems are TI-complete.

More generally, the same holds for any form family, symmetric or not, whose forms have explicit split blocks [[0, αI], [βI, 0]] of polynomial size. Families with sublinear-power Witt index stay open, for example the Lorentz groups O(n, 1).

## What is not covered

- **O(n, ℝ).** The Witt index is 0, so there is no hyperbolic block. Whether TI_O = TI there is Question 7.1, and it is untouched here. Its five actions are linear-equivalent by our [research manuscript].
- **Unitary U(n, ℂ).** The form is sesquilinear, so Theorem 1.10 does not apply. Lysikov–Walter give TI_U ⊆ TI. Five-action equivalence for U is CGQTZ Theorem 1.12, and its linear-length version is in our `PROOF-UNITARY.md`.
- **Linear length for Sp.** Membership goes through Futorny–Grochow–Sergeichuk tensor systems, which blow up the size polynomially. So only polynomial-time equivalence is claimed. The linear-length question for Sp (the CGQTZ line-387 remark, for Sp) remains open. The GL → Sp hardness direction and the Lemma 1 collapses are linear.
- **Status.** Informal, with no Lean proof. The Sp padding for action (i) is already in Lean (`TIEqTISp.lean`, `ti_eq_tisp`). Lemma 1 and the shared-mode case of Lemma 2 are not formalized.
