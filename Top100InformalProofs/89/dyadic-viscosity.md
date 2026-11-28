# Finite-time blow-up in a dyadic lattice with degenerate viscosity

This is the explicit dyadic lattice model. The proof carries its stated weighted-space and solution-class hypotheses.

## Model (fixed, finite rational description)
Fix λ > 1 rational (say λ = 2). Let U(t,k) ∈ ℤ[t,k₁..k_s] be a universal DPRM polynomial: t ∈ K ⟺ ∃k ∈ ℕ^s, U(t,k) = 0.
Modes:
- a catalyst z;
- site modes x_{t,k} for (t,k) ∈ ℕ×ℕ^s;
- chain modes a_{t,k,n} for n ≥ 1.

Set a_{t,k,0} := x_{t,k}. Write A for the skew nearest-neighbour adjacency **in the k-directions only**: (Ax)_{t,k} = Σ_i (x_{t,k−e_i} − x_{t,k+e_i}), with absent neighbours dropped. The equations are

- ż = 0
- ẋ_{t,k} = z (Ax)_{t,k} − λ x_{t,k} a_{t,k,1}
- ȧ_{t,k,n} = λ^n a_{t,k,n−1}² − λ^{n+1} a_{t,k,n} a_{t,k,n+1} − U(t,k)² λ^{2n} a_{t,k,n}  (n ≥ 1)

The quadratic part B satisfies ⟨B(v,v),v⟩ = 0 formally:
- the z·A terms vanish by skew-symmetry;
- the site–chain exchange −λx²a₁ + λx²a₁ cancels;
- the dyadic terms telescope.

The only linear term is a nonnegative dissipation with polynomial symbol U(t,k)²λ^{2n}, an anisotropic or degenerate viscosity. The whole system is described by finitely many integers: λ, the coefficients of U, and s. The datum for input t is z = 1 and x_{t,0} = 1, with every other mode 0. This is rational and finitely supported.

Phase space: X = { Σ x² + z² + Σ λ^{2n} a_{t,k,n}² < ∞ }. Blow-up means the maximal X-solution has finite lifetime.

## Theorem S1
For the fixed system above, {t : the solution from datum e_t blows up in finite time} = K. It is Σ⁰₁-complete.

### Proof
**0. Local theory.**
- Galerkin truncation together with the a priori estimate Y′ ≤ C(Y^{3/2} + Y), Y = ‖·‖_X², gives local X-solutions. For the inviscid dyadic sum, reindexing gives (1−λ^{−2}) Σ λ^{3n} a_{n−1}² a_n ≤ C Y^{3/2}.
- Uniqueness holds in ℓ² for X-bounded solutions, because the difference estimate only needs sup λ^n|a_n| ≲ ‖a‖_X.
- The energy inequality E(t) ≤ E(0) = 2 holds for X-solutions. The telescoping is legitimate because λ^n a_n² a_{n+1} → 0 in X.
- Different t-slices never interact (A acts only in k), so only slice t is excited.

**1. t ∉ K ⇒ global.**
- Every site has |U(t,k)| ≥ 1, so the dissipation is at least λ^{2n} on every chain.
- In d/dt ½Σλ^{2n}a_n², bound the drive term by λ^{3n}|a_n||a_{n−1}|² ≤ √2 λ^{3n}|a_n||a_{n−1}| ≤ ¼λ^{4n}a_n² + Cλ^{2(n−1)}a_{n−1}². Bound the transfer term by λ^{3n+1}a_n²|a_{n+1}| ≤ ¼λ^{4n}a_n² + Cλ^{2n}a_n². Both are absorbed by the dissipation, up to a Gronwall term.
- The site part is a bounded skew operator plus a bounded exchange.
- Hence Y(t) ≤ Y(0)e^{Ct}, and the solution is global.

**2. t ∈ K ⇒ blow-up.** Pick a witness k* with U(t,k*) = 0, so chain k* is inviscid. Write d = |k*|, b₀ = x_{t,k*} and b_n = a_{t,k*,n}.

*(a) The witness site is reached.* Each component is C^∞ in t, because its m-th derivative is a polynomial in finitely many components. The order-d Taylor coefficient of b₀ at 0 is ((zA)^d e_0)_{k*} = (−1)^d·(multinomial) ≠ 0. Nonlinear terms enter only at order > d, because a_{k,1} = O(t^{2|k|+1}). So b₀(t) ≠ 0 on (0,ε).

*(b) Positivity.* ḃ₁ = λb₀² − (λ²b₂)b₁ is linear in b₁ with forcing ≥ 0 that is not identically zero, so b₁ > 0 on (0,ε). Inductively b_n ≥ 0, with b_n > 0 for small t > 0.

*(c) Monotone tails.* For N ≥ 2 let E_N = Σ_{n≥N} b_n². Then dE_N/dt = 2λ^N b_{N−1}² b_N ≥ 0, and E_N ≤ 2. Fix t₀ with η := E₂(t₀) > 0.

*(d) Cascade lemma.* Put δ_N = η/(4N²). Suppose E_N ≥ η′ on [τ,∞), and suppose E_{N+1} < η′ − δ_N on [τ, τ+Δ_N] with Δ_N = 1/(√2 λ^{N+2}) + 2√2 λ^{−N} δ_N^{−2}. Then:
- b_N² = E_N − E_{N+1} > δ_N on that interval;
- ḃ_{N+1} ≥ λ^{N+1}δ_N − √2 λ^{N+2} b_{N+1}, so b_{N+1} ≥ β := δ_N/(2√2λ) after time 1/(√2λ^{N+2});
- after that, dE_{N+1}/dt ≥ 2λ^{N+1}δ_N β = λ^N δ_N²/√2, which would push E_{N+1} past 2 within the remaining time. Contradiction.

So E_{N+1} ≥ η′ − δ_N by time τ + Δ_N.

*(e) Finite-time contradiction.* Iterate from N = 2 at t₀. With T* := t₀ + Σ_N Δ_N < ∞ (Δ_N = O(N⁴λ^{−N}), summable for every λ > 1), we get E_N(T*) ≥ η − Σδ_N ≥ 3η/4 for every N. That is impossible for an ℓ² sequence. So the X-solution cannot be continued to T*: it blows up in finite time. ∎

**Hardness and membership.** t ↦ datum is computable and the blow-up set equals K. Hence the blow-up set is Σ⁰₁-complete.
