# Decidability with a computable gap in a classical-flag architecture

The scope is the specified architecture and entanglement predicates.

## Setting

As in robust.md Thm C:
- ρ_{t,m} = Σ_{|w|=m} |w⟩⟨w| ⊗ X_{t,w}, with X_{t,w} = ℓ_t M_{w₁}⋯M_{w_m} r;
- fixed M_a, r and fixed endpoint dimensions d_L, d_R;
- left end ℓ_t algebraic and computable;
- ρ ⪰ 0 and Tr X_{t,w} = q^{-m} (uniform flags; this is automatic when all proper marginals are maximally mixed).

Let φ ∈ {N_{L|rest}, d_SEP}, and let Φ_m(t) = E_w φ(σ_w), where σ_w = q^m X_{t,w}. Then:
- N(ρ_{t,m}) = Φ_m for φ = N;
- dist(ρ_{t,m}, SEP) ≤ Φ_m for φ = d_SEP, with Φ_m = 0 when ρ_{t,m} is separable (robust.md F2).

## Theorem G

Let θ : ℕ → ℚ_{>0} be computable. For each quantifier pattern Q ∈ {∃, ∀, ∃^∞, ∀^∞}, no such family satisfies both:
- t ∈ K ⇒ Q m: Φ_m(t) ≥ θ(t) (in particular, if negativity or distance ≥ θ(t));
- t ∉ K ⇒ ρ_{t,m} separable for all m.

In other words, every promise problem "θ-gapped entangled versus always separable" is decidable.

**Proof.**
1. Fix t and θ = θ(t).
2. φ is Lipschitz on the compact state space: d_SEP is 1-Lipschitz, and N is (d_L/2)-Lipschitz in trace norm. So a multivariate Bernstein polynomial Π with rational coefficients and |Π − φ| ≤ θ/4 has degree computable from θ. Its coefficients are computable to any precision, because φ is a computable real function.
3. Set E_m = E_w Π(σ_w). The tensor-power identity (robust.md Thm C) gives E_m = u_t T^m v. Here T is fixed for each degree, u_t is algebraic and computable, and |E_m − Φ_m| ≤ θ/4.
4. E_m is bounded, so the bounded-exponential-polynomial lemma (robust.md) gives E_m = g(m) + τ(m). Here g(m) = Σ_{|λ|=1} c_λ λ^m and τ(m) = Σ_{|λ|<1} p_λ(m) λ^m, with all data algebraic and exactly computable.
5. Compute M₀ such that |τ(m)| < θ/8 for all m ≥ M₀. This is an explicit bound from the coefficient sizes and max|λ| < 1.
6. Closure lemma: the closure of {Λ^m : m ≥ M₀} equals the closure H of {Λ^m : m ≥ 0}. A closed subsemigroup of a compact group is a group, and Λ^{M₀} ∈ H. H is computable, because the relation lattice of the λ's is computable (Masser). So s := max_H G, where g(m) = G(Λ^m), equals sup_{m≥M₀} g(m) and is computable to any precision. The same holds for min_H G and for the mean square.
7. Decide each pattern. In the non-halting case Φ ≡ 0, so |E_m| ≤ θ/4 for all m.
   - **∃:** if some m < M₀ has E_m ≥ 3θ/4 (exact algebraic comparison), answer "halts". Otherwise compare s with the thresholds 5θ/8 and 3θ/8. Halting forces s ≥ 3θ/4 − θ/8 = 5θ/8. Non-halting forces s ≤ θ/4 + θ/8 = 3θ/8.
   - **∃^∞:** compare s with the same thresholds.
   - **∀^∞:** compare min_H G (≥ 5θ/8 in the halting case, and |·| ≤ 3θ/8 otherwise). Alternatively use robust.md's Cesàro mean square.
   - **∀:** check m = 1 exactly.

In each case the promise gap leaves a margin of θ/4, so approximate evaluation suffices. ∎

**Corollary (critical scale).** In this architecture the halting information lives strictly below every computable scale. For halting t, sup_m N(ρ_{t,m}) has no computable positive lower bound. The exact problems nevertheless reach the full Σ1/Π1/Π2/Σ2 classification (R-H1-hierarchy). This gives a two-sided dichotomy:

> exact entanglement of a fixed TI classical-flag MPDO family: Σ⁰₁/Π⁰₁/Π⁰₂/Σ⁰₂-complete according to the length quantifier;
> θ-robust (any computable θ > 0, any quantifier): decidable.

## Thermodynamic limit (Theorem A family of robust.md)

- **Limit of negativity.** N_m → N_∞(t). The witness prefix weights (s+1)^{-(ℓ+1)} are m-independent and the tail is O((s/(s+1))^m), so the limit exists. N_∞ is left-c.e., and N_∞(t) > 0 iff t ∈ K (Σ1-complete). By Theorem G, N_∞(t) has no computable lower bound on K.
- **Entanglement of the limit (KILL).** Every finite-site marginal is maximally mixed. So the thermodynamic-limit state on the quasi-local algebra (any fixed finite window, m → ∞) is the tracial state, which is a product. Thus "is the limit state entangled?" is always "no". The halting signal survives only as a limit of global, all-site entanglement, not as entanglement of the limit, because negativity is not weak*-continuous.
- **Correlation length (KILL).** All k-point functions with k < m+2 vanish (maximally mixed proper marginals), so every correlation length is 0. In any fixed-bulk architecture the bulk decay rates are spectral data of the t-independent transfer operator. The boundary decides only which modes appear (u_t Π_λ ≠ 0, decidable). So correlation length is decidable.
