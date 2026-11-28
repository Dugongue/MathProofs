# Reduction of unique products to Bieberbach cores

This is the general reduction. The separate low-dimensional census requires its own certificates.

## 2. Definitions and the reduction

**Lemma A (hyperplane stabilisers) [proved, elementary].** Let Γ ⊂ Isom(Rⁿ) be Bieberbach with lattice Zⁿ and holonomy G. Let μ be a primitive integer functional, K ≤ G, and ε: K → ±1 with μA = ε(A)μ for all A ∈ K.
- Γ_K acts on R by x ↦ ε(A)x + μ(t).
- The stabiliser H of the affine hyperplane E = {μ = x0} is a Bieberbach group of dimension n−1, with lattice Zⁿ ∩ ker μ.
- Its holonomy is H̄ = {A ∈ K⁺ : μ(t_A) ∈ Z} ∪ {A ∈ K∖K⁺ : μ(t_A) ≡ 2x0 mod Z}, where K⁺ = ker ε.
- b1(H) = dim V^{H̄} − [H̄ ⊆ K⁺].
- Every codimension-1 Bieberbach subgroup arises this way. Restriction to E is injective, because a kernel element would be a reflection or a nonzero translation fixing E.
- The Calabi kernels of finite-index subgroups are exactly the case ε = 1. That case covers only 2 of the 66. The twisted case ε ≠ 1 is what settles the other 60.

**Definition.** A Bieberbach group Γ with holonomy representation ρ: G → GL(V) is **minimally fpf** if V^G = 0 and V^K ≠ 0 for every proper K < G. A **core** is a minimally-fpf primitive Bieberbach group that contains no primitive subgroup of smaller dimension.

**Theorem B (core reduction) [proved].**
(i) Every non-diffuse Bieberbach group contains a core.
(ii) UP ⇔ diffuse holds for all Bieberbach groups iff every core is non-UP.
(iii) Any UP core answers KR Question 1 positively.

*Proof.* Let Γ be non-diffuse. By KR it contains a primitive subgroup. Among its primitive subgroups, choose H minimising (dimension, |holonomy|) lexicographically.
- If K < hol(H) has V^K = 0, then H_K = π⁻¹(K) is primitive with smaller holonomy. So H is minimally fpf.
- A primitive subgroup of H of smaller dimension contradicts minimality.
So H is a core. Non-UP passes to supergroups and diffuse ⇒ UP (Bowditch), which gives (ii). Every core is non-diffuse (b1 = 0, so not locally indicable), which gives (iii). ∎

Note: "minimal by index" is useless, since primitive groups have infinite descending chains of finite-index primitive subgroups with the same holonomy. Hence the (dimension, |holonomy|) order.
