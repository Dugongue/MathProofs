# Extension complexity for virtually nilpotent classifying spaces

The non-virtually-abelian branch uses the cited group-equation undecidability theorem. The virtually abelian case here concerns dimension two.

## 2. N1, N1′, N2: non-virtually-abelian Nil π₁ is Σ⁰₁ at every D

**Theorem N1 (P, 92%).** Let Y be finite with Γ = π₁Y f.g. virtually nilpotent and not virtually abelian. Then EXT_D(Y) is Σ⁰₁-complete for every D ≥ 2.

*Proof.*
1. EXT_D(Y) is c.e. for every finite Y (UNIFIED Part II).
2. Dimension-≤ 2 instances are instances, and EXT₂(Y) ≡ DP_c(Γ) (R-H3 Lemma L; UNIFIED Part III row 1, A 95%). So DP_c(Γ) ≤ EXT_D(Y).
3. Γ contains a non-virtually-abelian nilpotent subgroup, namely N. GMO Thm 4.16 then gives a ring of algebraic integers O that is e-interpretable in Γ. Koymans–Pagano make DP(O) undecidable, indeed Σ⁰₁-complete. ∎

No assumption on π_{≥2} or on the π₁-action is used. **So N1 holds outside K2's "VN through D−1" hypothesis too.** Example: N³∨S² has π₂ = ℤ[H₃], on which the action is not nilpotent, and it is still Σ⁰₁ at every D ≥ 2.

**N1′ (P, 97%).**
- π₁(W_N) = N for D ≥ 2.
- The rationalisation of the nilpotent space W_N has π₁ = N ⊗ ℚ, the Mal'cev completion. It is non-abelian iff the Mal'cev Lie algebra 𝔫 is non-abelian, iff γ₂N is infinite, iff Γ is not virtually abelian.
- An H-space has abelian π₁, so Sh(W) is not H, and the Σ⁰₁-rung is predicted.
- Theorem T is therefore correct on this whole block, at every D, with no condition.

**N2 (P, 97%).** For f.g. nilpotent N: N′ finite ⟺ Z(N) has finite index (FC argument, audit-merged-1 §1b) ⟺ N is virtually abelian. Hence:
- **class is not the invariant.** H₃(ℤ)/⟨z^m⟩ (class 2, N′ = ℤ/m) has the central ℤ² = ⟨x^m, y^m⟩ of index m³ (because [x, y^m] = z^m = 1). So its shadow is K(ℚ²,1) at D = 2, which is H, giving the NP-rung. The same holds for Q₈ × ℤ^r and for every central product of a finite group with ℤ^r.
- **the invariant is h(γ₂N)** (equivalently rank(γ₂N/γ₃N) > 0, by Lemma Span in audit-merged-1 §1f):
  - h > 0 ⇒ Σ⁰₁ at every D;
  - h = 0 ⇒ the tier is decided by the higher layers, through §4.
- **Mal'cev coordinates.** The Σ⁰₁ gadget is the commutator form γ₁/γ₂ × γ₁/γ₂ → γ₂/γ₃ ⊗ ℚ ≠ 0. This is the crossover row "infinite-order deviation ⇒ Σ⁰₁ (QBLIN)". Torsion in γ₂ is invisible to the rational shadow and gives only NP (Lemma C / Lemma VA).

**Answer to the brief's question.** A class-2 π₁ forces NP-hardness, by GR on a finite non-abelian quotient. It forces Σ⁰₁ exactly when γ₂ is infinite. The rational shadow "behaves differently" from the class only in the sense of N2: it forgets finite derived subgroups, and that is the correct behaviour. No class-2 example where the shadow mispredicts was found (§5).

## 3. N3: D = 2, virtually abelian Γ

**N3 (P, 92%).** Γ is f.g., virtually abelian and non-abelian.
- **Membership.** Fix a free-abelian A ⊴ Γ of finite index and a transversal s.
  1. Guess the coset of every variable.
  2. Check the word in the finite group Γ/A.
  3. Each equation becomes Σ ± ρ(h_k) a_{i_k} = c over ℤ^r, with ρ(h) from a fixed finite set and constants of linear size.
  4. Solve the integer linear system in P (Kannan–Bachem).

  This is Ψ-vn's membership.
- **Hardness.** Γ/Γ^{em} is non-abelian for large m (audit-hbz-vn §3c, Klein-bottle caveat). Apply GR, using finite-width substitution for the verbal subgroup.

So the D = 2 case of the old Lemma A^G was never conditional.
