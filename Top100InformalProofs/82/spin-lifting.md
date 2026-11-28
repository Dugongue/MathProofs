# Integral lifting to the two-sphere in dimension six

The Pontryagin-class criterion retains the exact domain and cohomology hypotheses.

## 1. Integral lifting to S² on 6-manifolds

Notation. s ∈ H²(S²;ℤ) is the generator. For u ∈ H²(X;ℤ), L_u is the complex line bundle with c₁ = u. KSp is quaternionic K-theory. q: KU → KSp is quaternionification E ↦ E ⊗_ℂ ℍ.

**Lemma 1.1 (KSp criterion).** Let X be a CW complex of dimension ≤ 6 and u ∈ H²(X;ℤ). Then u = g^*s for some g: X → S² if and only if q(L_u − 1) = 0 in K̃Sp⁰(X).

*Proof.*
1. S² = Sp(1)/U(1), so there is a fibration S² → BU(1) → BSp(1), and the fibre inclusion S² = CP¹ → CP^∞ is an isomorphism on H².
2. A map X → BU(1) is homotopic to a map into the fibre if and only if its composite to BSp(1) is null. That composite classifies L_u ⊗_ℂ ℍ.
3. The fibre of BSp(1) → BSp is Sp/Sp(1). This is 6-connected, since Sp(2)/Sp(1) = S⁷ and the later quotients are higher spheres. So for dim X ≤ 6, an Sp(1)-bundle is trivial if and only if it is stably trivial, that is, iff q(L_u) − q(1) = 0. ∎

**Theorem 1 (exact criterion).** Let M be a closed oriented smooth 6-manifold and u ∈ H²(M;ℤ).

(a) If u = g^*s, then u² = 0. If moreover M is spin, then ⟨p₁(M)u,[M]⟩ ∈ 48ℤ.

(b) Suppose M is simply connected, and u² = 0 in H⁴(M;ℤ). Then:
   - if M is nonspin, u = g^*s for some g (Li–Pan–Wu, Proposition 4.4(1));
   - if M is spin, u = g^*s for some g if and only if ⟨p₁(M)u,[M]⟩ ≡ 0 (mod 48).

Note that for u² = 0 we have u³ = 0. Wall's congruence p₁(x) ≡ 4x³ (mod 24) then gives p₁(u) ∈ 24ℤ, so the condition says that the integer p₁(u)/24 is even.

*Proof.*

**Step 1: the Umkehr invariant.**
- Let M be spin. The KO-orientation gives π_!: KO⁴(M) = KSp⁰(M) → KO⁻²(pt) = ℤ/2.
- q is a map of KO-module spectra, since q(V ⊗_ℝ E) = V ⊗_ℝ q(E). So it commutes with the Umkehr maps built from the KO Thom class: π_!(q(L_u − 1)) = q(π_!^{KU}(L_u − 1)).
- Here π_!^{KU} uses the complexified spin orientation. So π_!^{KU}(L_u − 1) ∈ KU⁻⁶(pt) ≅ ℤ is the index of the spin Dirac operator twisted by L_u − 1.
- By Atiyah–Singer this index is ⟨Â(M)(ch L_u − 1),[M]⟩ = ⟨u³/6 − p₁(M)u/24, [M]⟩. When u² = 0 it equals −p₁(u)/24.

**Step 2: q is onto on the coefficient π₆.**
- On coefficients, q: π₆KU = K̃U(S⁶) → K̃Sp(S⁶) = π₆KSp ≅ ℤ/2. By clutching this is π₅(U) → π₅(Sp), induced by U(n) ⊂ Sp(n).
- The fibration U → Sp → Sp/U gives the exact sequence π₅U → π₅Sp → π₅(Sp/U).
- By Bott, Ω(Sp/U) ≃ U/O, so π₅(Sp/U) = π₄(U/O) = 0. Hence q is onto ℤ/2.
- Since q is additive, q(k) = k mod 2. So ε(u) := π_!(q(L_u − 1)) = p₁(u)/24 mod 2.

**Step 3: proof of (a).** If u = g^*s, then u² = g^*(s²) = 0, and q(L_u − 1) = 0 by Lemma 1.1. So for spin M, ε(u) = 0.

**Step 4: proof of (b), spin case.**
1. The bundle L_u ⊗ ℍ is classified on M^{(4)} by c₂ = −u². This is because HP^∞ → K(ℤ,4) is 5-connected. Since H⁴(M) → H⁴(M^{(4)}) is injective, u² = 0 makes the bundle trivial on M^{(4)}.
2. By Smale, a simply connected closed smooth 6-manifold has a handle decomposition with no 1-handles and no 5-handles, and with one 6-handle. So M^{(5)} = M^{(4)} and M/M^{(4)} = S⁶.
3. The exact sequence of the pair shows that x := q(L_u − 1) = c^*(y) for some y ∈ K̃Sp(S⁶) ≅ ℤ/2, where c: M → S⁶ is the collapse map.
4. π_!(c^*y) is the Thom/suspension isomorphism applied to y, since the KO Thom class restricted to a disc is the Bott class. So π_!∘c^* is an isomorphism.
5. Hence x = 0 ⟺ ε(u) = 0 ⟺ p₁(u)/24 is even. By Lemma 1.1, this is the claimed criterion.
   - *Alternative to Smale:* use the Atiyah–Hirzebruch spectral sequence. E^{5,−5} = H⁵(M;ℤ/2) = H₁(M;ℤ/2) = 0, so F⁵ = F⁶ = im c^*.

**Step 5: proof of (b), nonspin case.** This is quoted from Li–Pan–Wu. In the spectral sequence above, E_∞^{6,−6} = H⁶(M;ℤ/2)/Sq²H⁴(M;ℤ/2). Here Sq² = w₂ ∪ − maps onto H⁶ by Poincaré duality, so E_∞^{6,−6} = 0. ∎

**Consistency checks.**
- *Independence of the integral lift.* Li–Pan–Wu's Θ₀ is defined on mod-2 classes. Our ε depends only on ū among integral square-zero lifts. Indeed, if u and u + 2v are both square-zero, then uv = −v², so v³ = −uv² = u²v = 0. Wall's congruence then gives p₁(v) ∈ 24ℤ, so p₁(u+2v)/24 − p₁(u)/24 = p₁(v)/12 is even.
- *Products.* For M = S² × N⁴ with N spin and u the S² class, p₁(u) = p₁(N)[N] = 3σ(N). This is ≡ 0 mod 48 by Rokhlin, which matches the obvious lift (the projection).
- *Stably parallelisable M.* Here p₁ = 0, which matches ManinPersistenceAndDegrees §4.

**Corollary 1.2 (exact degree sets for every simply connected source).** Let M be simply connected, closed and smooth. Put
- Λ(M) = {u ∈ H²(M;ℤ) : u² = 0, and (w₂(M) ≠ 0 or p₁(u) ≡ 0 mod 48)}.

Then D(M,(S²)³) = {⟨abc,[M]⟩ : a,b,c ∈ Λ(M)}. This set is symmetric, because composing with an antipodal map on one factor sends a to −a, and the conditions are invariant under that.

*Proof.* A map f = (f₁,f₂,f₃) gives a_i = f_i^*s ∈ Λ(M) by Theorem 1(a), and deg f = ⟨f^*(s₁s₂s₃),[M]⟩ = ⟨a₁a₂a₃,[M]⟩. Conversely, Theorem 1(b) realises each a_i ∈ Λ(M). ∎

So for each fixed d, "d ∈ D(M,(S²)³)" is an explicit system over ℤ, computable from M:
- u² = 0 in H⁴(M;ℤ), which is quadratic equations in the free part plus congruences for torsion;
- one linear congruence mod 48 per class, in the spin case;
- one cubic equation μ(a,b,c) = d.

This gives a direct Σ⁰₁ upper bound that does not enumerate simplicial maps. Hardness is the portfolio's.

---

## 2. Example: the integral problem sees p₁ mod 48

**Example 2.** Let M_ε be the closed simply connected smooth spin 6-manifold given by Wall's realisation theorem with:
- H²(M_ε;ℤ) = ℤ⟨U,b,c⟩ and b₃ = 0;
- cup cubic F = 6Ubc, so μ(U,b,c) = 1 is the only nonzero entry up to symmetry;
- p₁ = 24U*, that is, p₁(U) = 24 and p₁(b) = p₁(c) = 0.

Wall's conditions hold:
- μ(x,x,y) and μ(x,y,y) are both even, since every term carries a factor 2;
- 4μ(x,x,x) = 24x_Ux_bx_c ≡ 0 ≡ p₁(x) (mod 24).

The integral cohomology ring is that of (S²)³, whose own p₁ is 0. Then:

- The square-zero classes of M_ε are exactly the single-axis classes αU, βb and γc. In the ring of (S²)³, (x₁s₁+x₂s₂+x₃s₃)² = 2Σ_{i<j}x_ix_js_is_j.
- By Theorem 1, Λ(M_ε) = 2ℤU ∪ ℤb ∪ ℤc, because p₁(αU)/24 = α.
- Hence **D(M_ε,(S²)³) = 2ℤ**. The class triple (2U,b,c) gives degree 2, and degree 1 is impossible.
- Rationally, M_ε dominates (S²)³ exactly as (S²)³ does. In particular, no degree-one map exists although the integral cohomology rings are isomorphic.

This is consistent with the homotopy classification of Wall and Jupp, in which p₁ mod 48 is an extra homotopy invariant. M_ε is then not homotopy equivalent to (S²)³. This last point is cited from memory and was not re-read; Example 2 itself rests only on Theorem 1.

Moral for the target problem: an integral fixed-degree reduction must carry p₁ mod 48 in its gadgets. The portfolio's constructions are nonspin, or have p₁ = 0, so they avoid this. Theorem 1 shows they could also use spin sources with p₁ ≠ 0, at the price of one mod-2 linear condition per class. That condition can be absorbed into the gate system by doubling the U axis.

---
