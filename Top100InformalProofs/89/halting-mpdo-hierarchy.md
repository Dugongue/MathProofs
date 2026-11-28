# An arithmetic hierarchy in a fixed matrix-product density-operator bulk

This is an independently unaudited written construction in the stated translation-invariant model.

## Theorem H (exact-length hierarchy)

There is a fixed rational bulk (non-commuting, translation-invariant, diagonal physical index (a,g)), a fixed right end, and a left boundary row c_t computable from t. Together these define rational states ρ_{t,m}, m ≥ 1, with the following properties.
- Each ρ_{t,m} is positive definite and every proper marginal is maximally mixed.
- E_t := {m : ρ_{t,m} entangled across L|rest} is decidable uniformly in t.
- Each of the following holds for suitable fixed event sets:

| property of t | class | complete for |
|---|---|---|
| ∃m entangled | Σ⁰₁ | K |
| ∀m ≥ m₀(t) entangled (m₀ computable) | Π⁰₁ | co-K |
| ∃^∞ m entangled | Π⁰₂ | INF = {e : W_e infinite} |
| ∀^∞ m entangled | Σ⁰₂ | FIN |

The complements (∀ separable, ∃ separable, ∀^∞ separable, ∃^∞ separable) have the dual classes. In this family, "entangled" is equivalent to each of: "NPT across L|rest", "distillable" (all NPT 2⊗N states are distillable, Dür–Cirac–Lewenstein–Bruß 2000), "negativity > 0" and "E_D > 0". So the table holds for all of these.

**Upper bounds.** At a fixed m, entanglement is decidable: the state is block diagonal with two-qubit blocks, so the PPT test is exact. In general, Tarski–Seidenberg decides it (quantitative.md 3a). Counting the quantifiers then gives Σ1, Π1, Π2, Σ2.

## Construction

**Machine.** Take a fixed universal 2-counter (Minsky) machine M with states p, instructions INC/DEC with zero branch, a HALT state, and a no-op OUT state. On input x₀ = g(t) (g computable) it simulates program t. For the Π2 and Σ2 rows, program t enumerates W_t and passes through OUT once per new element. The time between consecutive configurations is unbounded but each is finite.

**Words.** A word has the form w = c₀ # c₁ # ... # c_j _^r, where each c_i = P_{p_i} a^{x_i} b^{y_i}. That is, configurations are written in unary, followed by r padding letters.

**Readout.**

f_t(w) = [DFA(w)] · ( z(w) − r + 1/2 − 2(m+K)·Pen_t(w) ) − [¬DFA(w)],

where:
- DFA checks four things: the format; that p₀ is the start state; that p_{i+1} = next(p_i, [x_i>0 or y_i>0, as tested]), so zero tests are regular because emptiness of a unary block is regular; that no # follows HALT; and that p_j ∈ Ev, the chosen event set.
- Pen_t(w) = (x₀−g(t))² + y₀² + Σ_i [(x_{i+1}−x_i−δ^a_i)² + (y_{i+1}−y_i−δ^b_i)²]. The δ_i ∈ {−1,0,1} are a finite function of p_i and of the block emptiness.
- z(w) = 1 + x'_{j+1} + y'_{j+1} is the length of "#c_{j+1}" minus one, computed from the last block and p_j. It is set to 0 if p_j = HALT.

**Sign lemma.** f_t(w) > 0 iff the following hold: DFA(w) holds, Pen = 0 (so c₀..c_j is the true run prefix, by determinism), p_j ∈ Ev, and 0 ≤ r ≤ z. Otherwise f_t(w) < 0.
- If Pen ≥ 1, then z ≤ m + K gives f ≤ m + K + 1/2 − 2(m+K) < 0.
- If Pen = 0, then f > 0 iff r ≤ z, since both are integers.

So E_t = ⋃_{j : p_j ∈ Ev} [ℓ_j, ℓ_{j+1} − 1], where ℓ_j = |c₀#...#c_j|. The windows tile [ℓ₀, ∞) exactly, each step owning the window up to the next step.

- Ev = {HALT}: E_t ≠ ∅ iff M halts (Σ1).
- Ev = all non-HALT states: E_t ⊇ [ℓ₀, ∞) iff M never halts (Π1, with m₀ = ℓ₀ = 1 + g(t)).
- Ev = {OUT}: E_t is infinite iff there are infinitely many outputs iff t ∈ INF (Π2).
- Ev = all states except OUT: E_t is cofinite iff there are finitely many outputs iff t ∈ FIN (Σ2). This uses the window tiling: each OUT step removes a nonempty window, and every other step contributes its window.

**Recognizability.** Each of the following is a rational (recognizable) series over ℚ, by standard closure:
- m and r;
- per-block counts x_i, y_i, summed over blocks with finite-state weights;
- cross terms Σ_i x_i x_{i+1}: guess one a in block i and one in block i+1;
- last-block counts.

Hadamard products, which give (m+K)·Pen and the DFA indicator times a polynomial, are recognizable, and so are linear combinations. Expanding (x₀ − g(t))² gives f_t = F₀ + g(t)F₁ + g(t)²F₂ with fixed series F_i. Taking the direct sum, the input enters only through the initial row (1, g(t), g(t)²) ⊗ fixed rows. Growth: |f_t(w)| ≤ C(1+g(t))²(m+1)⁴.

**Lifting to a state.** Use quantitative.md §1.2 ("general form") with ε_w = f_t(w)/(L_t β^m), where L_t = 3C(1+g(t))² and β = 2⁵. This gives a bond of 4 + (automaton dimension), keys by the sign trick, strict positivity, maximally mixed proper marginals, and "entangled at m iff ∃w, |w|=m, ε_w > 0". All of these are inherited verbatim, since that construction accepts any weighted automaton.
