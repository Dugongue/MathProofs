# Amann's conjecture on Theorem 2.2: proved for all k ≥ 2

**Status.** Informal proof. Publication priority has not been established.

**The conjecture.** Amann, *On quasi-isometric nilpotent Lie groups* ([arXiv:1710.04542](https://arxiv.org/abs/1710.04542)), §2: "We conjecture that the following theorem is true for all k ≥ 2."

> **Theorem 2.2** (stated and proved there for k ∈ {2, 3}). The minimal model (ΛV, d) with
> - V₀ = ⟨x₁, …, x_{2k+1}⟩, V₁ = ⟨n₁, …, n_{2k−1}⟩, V₂ = ⟨m⟩;
> - dxᵢ = 0, dnᵢ = xᵢx_{i+1};
> - dm = Σ_{i=1}^{2k−1} xᵢnᵢ + x_{2k}x_{2k+1}
>
> is non-graded and rigid: every simply connected nilpotent Lie group quasi-isometric to it is isomorphic to it.

**What Amann's proof needs.** His Steps 1–2 are written for general k and are correct:
- Pansu gives the same Carnot type, so any competitor W is 3-stage with dm = σ + p, p ∈ Λ²V₀, where σ := Σ_{i≤2k−1} xᵢnᵢ.
- Shifting nᵢ by multiples of x's kills every monomial of p except t·x_{2k}x_{2k+1}.
- If t ≠ 0, then W ≅ V. If t = 0, then W ≅ (ΛV, d̄) with d̄m = σ, the associated graded algebra.

So the conjecture is **equivalent** to the following statement, which Amann checked for k = 2, 3 with Sage by counting degree-3 algebra generators (6 vs 5 and 9 vs 8):

> **(★)** H*(ΛV, d) ≇ H*(ΛV, d̄) as graded algebras, for every k ≥ 2.

## Setup

**The two Lie algebras.**
- Let g₀ be the Lie algebra dual to (Λ⟨x₁..x_{2k}, n, m⟩, d̄). This is Amann's Theorem 2.1 algebra, of dimension 4k.
- Let y := x_{2k+1}.
- Then ḡ = g₀ ⊕ ℝ, so H(ḡ) = H(g₀) ⊗ Λ[y].
- The non-graded algebra is g = ℝY ⋉_δ g₀, where δ(X_{2k}) = M and δ = 0 on the other generators. δ is a derivation into the centre that kills [g₀, g₀].
- So CE(g) = CE(g₀) ⊗ Λ[y] with d_g = d + y∧θ, where θ is the degree-0 derivation with θ(m) = ±x_{2k}, zero on the other generators.

**Hochschild–Serre** (codimension-1 ideal). H^j(g) ≅ ker(θ|H^j(g₀)) ⊕ coker(θ|H^{j−1}(g₀)).

**Dichotomy.**
- If θ ≠ 0 on H*(g₀), then dim H*(g) < dim H*(ḡ), and (★) holds trivially.
- So **assume θ = 0 on H*(g₀)**. This is the case for k = 2, 3, by computer.
- Then for every class e choose h_e with dh_e = −θe, and set L(e) := e − y h_e. This gives H(g) = L(H(g₀)) ⊕ y·H(g₀) and L(a)L(b) = L(ab) + y·μ(a, b), with μ(a, b) ∈ H(g₀).

## Lemma 1 (normal form: the isomorphism test is linear)

**Statement.** H(g) ≅ H(ḡ) iff there is a linear φ : H^j(g₀) → H^{j−1}(g₀) with

  μ(a, b) = φ(ab) − φ(a)b − (−1)^{|a|} a φ(b)  for all a, b.  (⋆)

*Proof.*
1. **X is intrinsic.** N₂ := ker(Λ²H¹ → H²) = span{xᵢx_{i+1} : i ≤ 2k−1} in both rings. In g, dm = σ + x_{2k}y is not in Λ²H¹.
   - The decomposable elements of N₂ are supported on stars of the path P_{2k}. Their planes lie in X := ⟨x₁..x_{2k}⟩ and span it.
   - So any isomorphism Ψ maps X onto X, and maps y to cy + v with c ≠ 0.
2. **Normalise y.** Ψ⁻¹(y) = c′y + v″. The map α = (id on H(g₀), y ↦ c′y + v″) is an automorphism of H(ḡ) = H(g₀) ⊗ Λ[y]. Replacing Ψ by Ψ∘α gives Ψ(y) = y.
3. **Reduce mod y.** Ψ induces an isomorphism β of H(g₀) ≅ H/(y), so Ψ(a) = L(βa) + y·φ′(a).
   - Expanding Ψ(a)Ψ(b) = Ψ(ab) gives μ(βa, βb) = φ′(ab) − φ′(a)βb − (−1)^{|a|}βa·φ′(b).
   - Put φ = φ′∘β⁻¹ to get (⋆).
4. **Converse.** If (⋆) holds, a + yb ↦ L(a) + y(φ(a) + b) is an isomorphism. ∎

The solvability of (⋆) does not depend on the choice of L, since changing L changes μ by a coboundary.

## Lemma 2 (degree ≤ 2 of g₀)

1. **H¹(g₀) = X.**
2. **Every closed 2-form is m-free.**
   - If ω = m∧ℓ + ω′ is closed, then dℓ = 0, so ℓ ∈ X, and σ∧ℓ must be exact in the m-free complex.
   - But for ℓ_j ≠ 0 with j ≥ 2, σ∧ℓ contains the monomial x_{j−1}x_j n_{j−1} with coefficient ±ℓ_j. No m-free coboundary produces it: d(n_a n_b) = x_a x_{a+1} n_b − x_b x_{b+1} n_a would need a = b = j−1.
   - For ℓ₁: σ∧x₁ contains x_i x₁ n_i with i ≥ 3, which is never produced.
   - Hence θ = 0 on Z², so h = 0 on H¹ and H², and L(e) = e on m-free representatives.
3. **H²(g₀) = Λ²X/⟨edges⟩ ⊕ C/⟨σ⟩.**
   - Here C = span{cᵢ = xᵢnᵢ, c′ᵢ = x_{i+1}nᵢ, t_a = x_a n_{a+1} − x_{a+2} n_a}. These are distinct monomials, so they are linearly independent.
   - B² = ⟨edges⟩ ⊕ ⟨σ = dm⟩.
   - A basis is: the non-edge monomials x_a x_b; c₁, …, c_{2k−2}; all c′ᵢ; all t_a.
   - In H(g₀), c_{2k−1} = −Σ_{i≤2k−2} cᵢ, because σ is exact. In H(g), by contrast, Σᵢ cᵢ = ∓x_{2k}y.

## Theorem (★): H*(g) ≇ H*(ḡ) for every k ≥ 2

Write a = x_{2k−2}, b = x_{2k−1}, c = x_{2k}, p = n_{2k−2} (so dp = ab) and q = n_{2k−1} (so dq = bc). Let t := t_{2k−2} = a q − c p, which is closed because dt = −abc + cab = 0.

**The key cochain identity.**
1. **Two expansions.** b·t = −abq − bcp. Also d(pq) = abq − bcp, so b·t = −d(pq) − 2bcp and a·(bq) = d(pq) + bcp.
2. **A relation.** Hence b·t + 2a·c_{2k−1} = d(pq). Substitute the basis expression c_{2k−1} = bq = σ − Σ_{i≤2k−2} xᵢnᵢ.
3. **Result.** The basis tensor R := t⊗x_{2k−1} − 2 Σ_{i≤2k−3} cᵢ⊗x_{2k−2} has product

   t·x_{2k−1} − 2 Σ_{i≤2k−3} x_{2k−2}·cᵢ = d(pq) − 2x_{2k−2}σ = d(pq + 2x_{2k−2}m).

   The omitted term x_{2k−2}·c_{2k−2} = x_{2k−2}x_{2k−2}n_{2k−2} is zero on cochains. So R is a relation in H³(g₀), and its primitive r = pq + 2x_{2k−2}m has θr = ±2·x_{2k−2}x_{2k}.

**Summing (⋆) over R.**
1. **The φ(ab) terms cancel**, because Σλ[ax] = 0. The Σcᵢh_{eᵢ} terms in μ also cancel. So Σλ·μ = ±[θr] = ±2[x_{2k−2}x_{2k}].
2. **This class is nonzero**: it is a non-edge basis monomial, since the indices differ by 2.
3. **The gauge side** of (⋆) summed over R is

   −φ(t)∧x_{2k−1} − t·φ(x_{2k−1}) + 2 Σ_{i≤2k−3} (φ(cᵢ)∧x_{2k−2} + cᵢ·φ(x_{2k−2})).

**The trivial relations cᵢ⊗xᵢ** (with xᵢcᵢ = 0 on cochains, and μ = 0), for i ≤ 2k−3, force two things:
- φ(xᵢ) = 0, from the indecomposable cᵢ-component;
- φ(cᵢ)∧xᵢ ∈ ⟨edges⟩, i.e. **φ(cᵢ) ∈ ⟨x_{i−1}, xᵢ, x_{i+1}⟩**, so every index is ≤ 2k−2.

**Contradiction.** Compare the coefficient of the non-edge monomial x_{2k−2}x_{2k} in Λ²X/⟨edges⟩.
- The left side contributes ±2.
- φ(t)∧x_{2k−1} only produces monomials x_l x_{2k−1}.
- φ(cᵢ)∧x_{2k−2} only produces x_l x_{2k−2} with l ≤ 2k−2.
- The indecomposable terms do not contribute.
- So the right side contributes 0. Hence (⋆) has no solution, and by Lemma 1, H*(g) ≇ H*(ḡ). ∎

**Corollary (Amann's conjecture).** For every k ≥ 2, the nilpotent Lie group of Theorem 2.2 is non-graded and **QI-rigid**: any simply connected nilpotent Lie group quasi-isometric to it is isomorphic to it.
