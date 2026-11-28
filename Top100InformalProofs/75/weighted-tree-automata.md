# Finite-dimensional equivalence tests for weighted tree automata

The algorithm applies to the explicit field and representation model below.

## Field 4. Weighted tree automata

A weighted tree automaton (WTA) over a field F and a ranked alphabet Σ consists of:
- a state space V;
- for each σ ∈ Σ of rank r, a transition map μ_σ ∈ Hom(V^{⊗r}, V);
- final weights η ∈ V*.

An isomorphism is a g ∈ GL(V) conjugating all of these.

**Theorem 4.1 (rank dichotomy for automaton isomorphism).**
- **Max rank ≤ 1** (word automata): WTA isomorphism is in **P**.
- **Some symbol of rank ≥ 2:** it is **TI-complete**.

*Proof.*
1. **Rank ≤ 1.** The data are a tuple of matrices plus vectors and covectors under conjugation, i.e. module isomorphism over a free algebra with framing. That is in P (Chistov–Ivanyos–Karpinski; Brooksbank–Luks).
2. **Rank ≥ 2, membership.** A WTA is a fixed-shape tensor system of arity ≤ r + 1, so the ladder (Theorem L) plus FGS puts it in TI.
3. **Rank ≥ 2, hardness.** One binary symbol with η = 0 and no leaves gives exactly algebra isomorphism V⊗V → V under GL(V), which is TI-complete. ∎

**Theorem 4.2 (trim automata are easy).** For **trim** WTAs, isomorphism is in **deterministic polynomial time**. Trim means reachable (tree values span V) and observable (no nonzero vector killed by every context).

*Proof.*
1. **Uniqueness.** Minimal (trim) WTAs recognising the same tree series are isomorphic (Bozapalidis–Louscou-Bozapalidi, Myhill–Nerode for weighted tree automata over fields).
2. So for trim automata, isomorphism is the same as equivalence of the recognised series, which is decidable in polynomial time by linear algebra (Seidl 1990).
3. Trimness itself is checkable in polynomial time by reachable and observable span computations. ∎

*Reading.* All TI-hardness of tree automata lives in **non-minimal** automata: unreachable or unobservable state space. In automata-theoretic terms, TI is "isomorphism of redundant automata".

---
