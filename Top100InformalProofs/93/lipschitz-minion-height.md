# Support bounds and height in the Lipschitz minion

The small-dimensional bound and higher-dimensional obstruction concern the indicated Lipschitz model. The higher-dimensional conclusion is a lower bound on height.

## 0. Setup

- T = ℝ/ℤ with arc distance. T^n carries the max metric. S^d ⊂ ℝ^{d+1} has the chordal metric.
- 𝓛_d(C)(n) is the set of C-Lipschitz maps F : T^n → S^d with F(x + ½𝟙) = −F(x). Minors are F^π(y) = F(y∘π), for arbitrary maps π.
- The relaxed version (BGKR Def A.5) puts F [π] G iff ⟨F(x∘π), G(x)⟩ ≥ 0 for all x.
- Fix j : T → S¹ ⊂ S^d, j(s) = (e(s), 0, …) with e(s) = e^{2πis}. Write u = j for the unary element and e_c^{(N)} = j(y_c) for the projections.
- A height-1 chain homomorphism to P (BGKR: a "d-homomorphism") is a nonempty list λ(F) ⊆ [n], |λ| ≤ D, such that π(λ(F)) ∩ λ(F^π) ≠ ∅ for every arrow F → F^π.

## 1. Homotopy-level classification (where topology still sees minors)

Let H_d(n) = [T^n, S^d]_{ℤ2}.

| d | H_d as a minion | source |
|---|---|---|
| 1 | ℤ-affine: a ∈ ℤ^n with Σa_i odd | degree vector (KOWZ) |
| 2 | ℤ₂-affine: a ∈ ℤ₂^n with Σa_i = 1 | AFOTW 2504.07592, Prop 3.4 and Lemma 3.5 |
| ≥ 3 | has a constant family c_n = [j(x_1)] | PCSP.md Prop 6.2 |

For d ≥ 3 the homotopy H_t = (cos(πt/2) f, sin(πt/2) g) runs inside an antipodal S³ = S(ℂ²) ⊂ S^d and is Lipschitz with an absolute constant. So the constant family survives even modulo **C′-bounded** homotopy, for C′ above an absolute constant (lead-checked iteration i01 says the same). In particular, the brief's quotient "𝓛_d(L) modulo L′-bounded homotopy" satisfies every minor condition for d ≥ 3, so it is useless as a hardness minion (**kill**).

Remarks:
- For even d, f^*[S^d] = −f^*[S^d] in H^d(T^n; ℤ), so it vanishes. For d = 2 the surviving invariant is twisted and mod 2: H²(T^n/ℤ₂; ℤ^w) ≅ (ℤ/2)^{n−1}. That is why the d = 2 row is ℤ₂-affine, not ℤ-affine.
- The S³ quaternion Mal'cev operation xy⁻¹z gives nothing new on torus inputs. Its arguments j(x_i) lie in one U(1), so it restricts to the S¹ affine x − y + z, which already lives in 𝓛_1(3) and embeds in every 𝓛_d (Prop 6.1).

## 2. Theorem A (d = 2: an L-Lipschitz representative forces bounded support)

**Statement.** Let F ∈ 𝓛_2(L)(n) and let a = a([F]) ∈ ℤ₂^n be its AFOTW class. Then |supp a| ≤ 8L². More generally, for any target S^d where the binary-minor test below makes sense, the bound is (Σ_i |∂_i F| bound) · 4L.

**Proof.**

1. *Coordinate test.* a_i is the class of the binary minor F^{ρ_i}, where ρ_i sends i ↦ 1 and every other coordinate ↦ 2. The binary classes are e_1 = (1,0) and e_2 = (0,1). So a_i = 1 iff F^{ρ_i} ≄ e_2.
2. *Offsets.* For o ∈ T^n put g_o(y_1, y_2) = F(o + y_2𝟙 + (y_1 − y_2)e_i). Each g_o is equivariant, and translating o to 0 is an equivariant homotopy, so g_o ≃ F^{ρ_i}.
3. *Small oscillation gives class e_2.* Suppose that for some o every loop y_1 ↦ g_o(y_1, y_2) has chordal diameter < 1. Let h(y_2) = normalize(∫ g_o(y_1, y_2) dy_1).
   - The loop lies in a cap of angular radius 60°, so the mean has norm > ½ and h is never antipodal to g_o.
   - h is equivariant, because averaging commutes with the shift.
   - Hence the straight-line homotopy gives g_o ≃ h(y_2) ≃ e_2, since all equivariant S¹ → S² are homotopic.
4. So if a_i = 1, then on every diagonal line o + s𝟙 the function osc_i(x) = max_{t,u} |F(x + te_i) − F(x + ue_i)| reaches the value 1.
5. *Lower bound on ∫ osc_i.* osc_i is 2L-Lipschitz in the max metric, and along the diagonal line the max distance is |s − s′|. So osc_i ≥ ½ on an arc of length 1/(2L) of every diagonal line. The diagonal circles fibre T^n with fibres of length 1, so by Fubini ∫ osc_i ≥ 1/(4L).
6. *Upper bound on the sum.* osc_i ≤ ∫ |∂_i F| along the e_i-circle. For each unit vector e, Σ_i |∂_i⟨F, e⟩| ≤ L, by testing a sign direction of max-norm 1. Averaging over e ∈ S² (where E|⟨v, e⟩| = |v|/2) gives Σ_i |∂_i F| ≤ 2L a.e. So Σ_i ∫ osc_i ≤ 2L.
7. Combining steps 5 and 6: #{i : a_i = 1} ≤ 2L · 4L = 8L². ∎

**Corollary A1.** h*(2) = 1. Take λ(F) = supp a([F]), which has at most 8C² elements. It is nonempty because Σa = 1, and λ(F^π) ⊆ π(λ(F)) by additivity (AFOTW). The same holds for the relaxed minion: ⟨·,·⟩ ≥ 0 means the two maps are never antipodal, so the straight-line homotopy turns relaxed arrows into exact arrows on H_2.

**Corollary B (short reproof of AFOTW Thm 1.1, the BG conjecture for 4-colourable H, G).**
- BGKR Prop A.7 at p = 2, k = 4 gives a C-Lipschitz Φ(f) ∈ 𝓛_2(C) for each f ∈ Pol(C_L, K_4), with ⟨Φ(f)(x∘π), Φ(f^π)(x)⟩ > 0.
- I re-verified Prop A.7: positions differ by ℓ or ℓ+1 spacings, so the two palettes are disjoint; supports shrink under minors, so the inner product is positive.
- So f ↦ [Φ(f)] is an exact minion homomorphism Pol(C_L, K_4) → H_2 ≅ ℤ₂-aff.
- By Theorem A its image has essential arity ≤ 8C², and it contains no constants. BBKO Prop 5.14 then gives NP-hardness.
- This replaces AFOTW's combinatorial §5 (Thm 5.1, also O(ℓ²)). It uses nothing unverified from BGKR.
- The same argument at d = 1 gives (C_L, K_3).
- At k ≥ 5 it dies, because H_{k−2} is trivial (§1). That is exactly why chains are needed there.

## 3. Theorem C (d ≥ 3: no height-1 chain homomorphism)

**Statement.** There is an absolute C_0 (numerically ≈ 160) such that for every d ≥ 3 and every K ≥ 4 there is Φ_K ∈ 𝓛_d(C_0)(K) with

  Φ_K(t, …, t, s, t, …, t) = j(s)   (s in position c)   exactly, for every c ∈ [K] and all s, t ∈ T.

Consequently 𝓛_d(C_0) has no (1, D)-chain homomorphism to P for any D. Its relaxed version has none either, since it has more arrows.

**Lower-bound argument.**
- Suppose λ were such a list assignment, and take N ≥ D + 2.
- u → e_1^{(N)} along 1 ↦ 1, and λ(u) = {1}, so 1 ∈ λ(e_1^{(N)}). Write R = λ(e_1^{(N)}) ∖ {1}, so |R| ≤ D − 1.
- Pick r ∈ [N] ∖ (R ∪ {1}). Define π_c : [K] → [N] by c ↦ 1 and every other coordinate ↦ r. These minors are not surjective, which ordinary chains allow.
- Then Φ_K^{π_c} = e_1^{(N)}, and π_c(λ(Φ_K)) ⊆ {1, r} misses R. So the intersection must happen at 1, which forces c ∈ λ(Φ_K).
- This holds for every c, so |λ(Φ_K)| ≥ K > D. Contradiction. ∎

**Construction (S³ = S(ℂ²) ⊂ S^d, writing points as (P, Q)).**

| ingredient | definition | why it is Lipschitz |
|---|---|---|
| ν_i | median_k d(x_i, x_k) | 2-Lipschitz |
| φ_i | 8·(ν_i − 1/8)_+ | |
| i\* | an index with φ_{i\*} maximal | |
| A | (φ_(1) − φ_(2)) · e(x_{i\*}) | continuous because the coefficient vanishes at ties; 64-Lipschitz by the swap estimate c(x) + c(y) ≤ 32‖x − y‖ |
| B | (1 − \|A\|/a_0)_+ · e(x_1), with a_0 = ½ | |
| D(x) | max_{i,k} d(x_i, x_k) | |
| λ | clamp((D − 0.19)/0.05) | |
| σ | max + min − median of the real lifts, defined on {D < ¼} | 3-Lipschitz and translation-equivariant |

Then

  P = (1 − λ)e(σ) + λA,  Q = [λ(1 − |A|/a_0)_+ + (1 − λ)·|e(σ)|A| − A|] · e(x_1),  Φ_K = (P, Q)/|(P, Q)|.

- *Equivariance.* ν, D and λ are shift-invariant, while σ, x_{i\*} and x_1 shift by ½. So P and Q are odd.
- *Exactness on T_c (K ≥ 3).* On T_c we have ν_c = d(s,t), ν_{i≠c} = 0, σ = s and D = d(s,t). Hence A = φ(d)e(s).
  - d < 1/8: A = 0, λ = 0, so Φ = (e(s), 0).
  - 1/8 ≤ d < 0.19: the Q-term |e(s)φ − φe(s)| = 0.
  - 0.19 ≤ d < 0.24: φ(d) ≥ a_0, so B = 0, and P ∥ e(s) with positive coefficient.
  - d ≥ 0.24: Φ = normalize(φ(d)e(s), 0).
  - In every case Φ = j(s).
- *Norm bounded below.* Off λ ∈ (0,1) this is immediate. Inside, a small |P| forces A ≈ −((1−λ)/λ)e(σ). Then either |A| ≤ a_0/2, giving |Q| ≥ λ/2 ≥ 0.35, or |A| ≥ a_0/2, giving |Q| ≥ (1−λ)·2|A| − O(η) ≥ 0.02. Both coefficients in Q multiply the same unit e(x_1), so they add.
- *Numerical check* ([local reference omitted] output oddout.out), for K = 4…150:
  - exactness error ≤ 3e−15;
  - equivariance error ≤ 2e−14;
  - min |(P, Q)| ≥ 0.447;
  - estimated Lipschitz constant ≤ 160.1, not growing with K.

**Why d ≤ 2 escapes.** The construction needs a second complex slot Q orthogonal to S¹. In S², Q would be an odd real function that is nonzero along the whole diagonal, which is impossible. This matches Theorem A, and it is the same S³ ⊂ S^d that powers Prop 6.2.

## 4. Lemma S (symmetric elements, any d; P2 found the same)

- If F is S_n-invariant and n is odd, then the evenly spaced configuration x satisfies x + ½𝟙 = σ(x + 1/(2n)𝟙) for some permutation σ. So C ≥ 4n.
- If n is even, no symmetric element exists at all, because of the fixed configuration {w, −w, …}.
- With Austin's junta theorem or BGKR Lemma A.11, an element invariant under a group G has a nonempty G-invariant set of influential coordinates of size ≤ C/(2τ). So large transitive symmetry is excluded.
- Hence symmetric families cannot refute height 1. Theorem C has to use a non-symmetric, exactly-pinned family, and it does.
