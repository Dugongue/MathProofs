# The special-linear determinant test from Kummer quotients

The deterministic statement takes the factorization of the multiplicative group order as input.

## Setting
- G = (F_q^×)^3. δ(A,B,C) = (det A, det B, det C).
- D(T) = δ(Aut T(F_q)).
- [Lean, TISLDetCoset_20261123] S ≅_SL T ⟺ δ(g0)^{-1} ∈ D(T), for any g0 ∈ Iso_GL(T,S).
- The kernel of the GL³ action always lies in Aut T. Its det image is
  Σ = {(a^{n1}, b^{n2}, (ab)^{-m})} ⊆ D(T).
  For the balanced n×n×n format this is Σ = {(u,v,w) ∈ P³ : uvw = 1}, where P = (F_q^×)^n.

## Survivor 1: Theorem K (determinant step without DLOG)

**Lemma K1.** For the balanced format,
  φ(x,y,z) = (xyz, x^{(q−1)/d}, y^{(q−1)/d})
induces an isomorphism G/Σ ≅ C_{q−1} × μ_d × μ_d, where d = gcd(n, q−1).

*Proof.*
- ker φ: xyz = 1 and x, y ∈ P force z ∈ P, so ker φ = Σ.
- Orders: |G/Σ| = (q−1)³/((q−1)/d)² = (q−1)d² = |target|. ∎

For a general format n1×n2×m: G/Σ = coker of M = [[n1, 0, −m], [0, n2, −m]] over Z/(q−1). This is C_{q−1} × C_{gcd(e1,q−1)} × C_{gcd(e2,q−1)}, where e1 | e2 are the Smith invariants of M, e1 = gcd(n1,n2,m) and e2 ≤ n1·n2.

**Consequence.** For every prime ℓ ∤ e2, the ℓ-primary part of G/Σ is cyclic.

**Theorem K.** Input:
- T, S;
- one g0 ∈ Iso(T,S);
- any finite A ⊆ Aut T(F_q) with ⟨δ(A)⟩·Σ = D(T).

Then S ≅_SL T can be decided:
- in deterministic poly(n, log q, |A|) time, given the factorisation of q−1;
- in BQP with no extra input (Shor's algorithm factors q−1).

No discrete logarithm is taken in any group of order > ℓ^{O(log q)} with ℓ ≤ e2 ≤ n². If q is fixed, or q−1 is poly(n)-smooth, the factorisation is free and the whole step is in P.

*Proof.*
1. Put x = δ(g0)^{-1}. Map x and the δ(a), a ∈ A, by φ.
2. A finite abelian group is the direct product of its primary parts. So x ∈ H := ⟨φδ(A)⟩ iff, for every ℓ | q−1, the ℓ-component x_ℓ = x^{e_ℓ} lies in H_ℓ = ⟨φδ(a)^{e_ℓ}⟩. Here e_ℓ is the CRT idempotent, ≡ 1 mod ℓ^{v_ℓ(q−1)} and ≡ 0 mod the cofactor.
3. **ℓ ∤ e2.** H_ℓ sits inside a cyclic ℓ-group, whose subgroups form a chain. So x_ℓ ∈ H_ℓ ⟺ ord(x_ℓ) ≤ max_a ord(δ(a)_ℓ). Each order is found by repeated ℓ-th powers, at most v_ℓ(q−1) steps.
4. **ℓ | e2 (so ℓ ≤ n²).** The ℓ-part has rank ≤ 3 and exponent ℓ^{v}. Pohlig–Hellman digits live in μ_ℓ, which has size ≤ n², so brute force works. Membership is then Smith normal form over Z/ℓ^v. ∎

This repairs the gap in M4 §1, which says "an explicit element δ(g) cannot be put into L without a discrete log". The fix is to quotient by Σ first. Σ is always present, and it kills the ℓ-rank 2–3 that would otherwise make the problem DDH-like.

**Corollary K2** (with Lemma B [ours, tisl-sylow-localization]). TI_SL ≤ randomized TI-search plus FACTOR(q−1).
- Blinding: query h = search(T, gT) for uniform g. Then g^{-1}h is uniform on Aut T, so δ of it is uniform on D(T).
- O(log q) samples generate D(T)/Σ with probability 1 − 2^{-Ω(log q)}, since |D/Σ| ≤ (q−1)d².
- At fixed q: TI_SL ∈ BPP^{TI-search}. This was already known from Lemma B. The new part is only that large q adds no DLOG cost.

**Corollary K3** (ALTEQ_SL). For one GL_n acting on alternating or symmetric forms, D(φ) ⊆ F_q^× is cyclic. Membership is a single order comparison, so ALTEQ_SL ≤ ALTEQ-search plus FACTOR(q−1).

**K3 check.** [local reference omitted] compares the DLOG-free algorithm against brute-force closure in G (using a DLOG table, in the tester only).
- Range: all primes 3 ≤ q ≤ 113, n = 2..6, random subgroups ⟨Σ, h1..h3⟩ with small-order h's.
- Result: 69,600 membership checks (40,628 YES), **0 disagreements**.
- Only the balanced format was tested; the general format rests on the Smith normal form argument.

- **Weakest link:** factoring q−1 for the cyclic coprime part. Whether cyclic-subgroup membership in F_q^× can be done without factoring is not needed here and was not pursued.
- **Honest rank:** low (outside the top 30). It is a clean sharpening and tool lemma, and it closes the quantum/DLOG door.
