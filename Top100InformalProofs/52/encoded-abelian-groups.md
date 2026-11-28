# The counting-oracle reduction for encoded abelian groups

The reduction is stated in terms of the exact counting oracles. The subpolynomial implementation depends on the named unrefereed inputs and on wire bounds for specific encodings.

## Setting: encoded abelian groups

An **encoded finite abelian group** is a triple (G, ι, L), where ι : G → {0,1}^L is injective, the image V = ι(G) is the set of valid codes, and the group law is a function on codes. Write n = |G|. Note that L may exceed log₂ n.

**Definition (linear wire complexity).** (G, ι) has *wire complexity W* if each of the following admits a **parsimonious** BTN (in the sense of LZR Def. 2.1):
- the validity relation 1[x ∈ V];
- the addition relation 1[x+y = z] on valid codes;
- equality to a hard-wired constant.

Each network must have:
- ≤ W edges;
- max degree ≤ W^{9/10};
- poly(W) vertices;
- local entries computable in time 2^{O(W^{9/10})};
- description length 2^{o(L)}.

The family is **linear-wire** if W = O(L).

### Definition (weighted linear-relation counting oracle CNT_k)

A query consists of:
- a target code g;
- signs ε ∈ {±1}^k;
- a partition of [k] into blocks B of size ≤ 2;
- for each block, an auxiliary bit-block s_B ∈ {0,1}^{r_B}, a prefix pin on s_B, and a weight circuit w_B(s_B, (x_i)_{i∈B}) with values in R = (Z/2^P)[z]/(z^ℓ), where P, ℓ = poly(L) and the circuit has size 2^{O(L/m)}.

The answer is

  Σ_{s} Σ_{x_1,…,x_k ∈ V, Σ ε_i x_i = g} ∏_B w_B(s_B, x_B)  ∈ R.

This is exactly the family of sums that LZR evaluate: A_η, B_η, J_η in Stage I, and Z_Q (with prefix pins) in Stage II. It is defined purely in terms of the group law and *label predicates*. It makes sense in Shoup's generic-group model once label functions are allowed.

---

## Theorem D1-B (unconditional reduction; this pins down the boundary)

**Statement.** Let (G, ι, L) be an encoded finite abelian group and 2 ≤ m ≤ L. There is a deterministic algorithm that, using
- 2^{O(L/m)}·poly(L) queries to CNT_{4m+1}, and
- 2^{O(L/m)}·poly(L) further bit operations and group operations,

computes all of the following:
- (a) n = |G|;
- (b) an explicit generating set U ⊆ G with |U| = N = O(m² + m·(16n)^{1/m}) ≤ O(m² + m·2^{(L+4)/m});
- (c) the relation lattice L_U = ker(Z^N → G);
- (d) the Smith form G ≅ ⊕ Z/n_i, together with an explicit basis;
- (e) for any P, Q ∈ G, whether Q ∈ ⟨P⟩, and if so log_P Q.

**No D.1, no GRH, no randomness.** Taking m = L gives poly(L) queries of arity O(L).

**Status.** Proved, modulo the routine verifications listed in the proof. Confidence 0.8.

### Proof

**(a) Order.** One CNT_1 query with weight 1 gives |V| = n.

**(b) Stage I for an arbitrary encoding.** This is D2's lane. Here is my version, which does not depend on encoding density.
- Let L' = 2·3^κ ≥ L be minimal and F = GF(2^{L'}) = F_2[x]/(x^{2·3^κ}+x^{3^κ}+1). That trinomial is irreducible over F_2 for every κ ≥ 0 (classical), so the construction is explicit and deterministic.
- **Membership hash.** Seeds (α_i, β_i) ∈ F^* × F give h_i(x) = α_i x + β_i, where x is the code viewed in F and F is ordered as integers in [0, 2^{L'}). Set F_i(S) = {g : h_i(ι g) < T} with T = ⌈2^{L'} q*/n⌉.
  - For distinct codes, (h(x), h(y)) is uniform on distinct ordered pairs, which is exactly LZR's one-point and two-point law.
  - Lemma 3.2 goes through verbatim with p replaced by 2^{L'}. The step "n ≤ p/O(1)" is never needed: only θ = T/2^{L'} and q_blk = nθ enter the moments.
- **Address tag.** This is the new ingredient. A second independent seed (γ_i, δ_i) gives t_i(x) = top c bits of γ_i x + δ_i, with c = ⌈log₂(m q_blk²)⌉ + 10 = 2L/m + O(log m).
  - Let Coll(S) = #{(i, D ≠ D') : D, D' ∈ F_i(S), t_i(D) = t_i(D')}.
  - Then E[Coll] ≤ m q_blk² 2^{−c} ≤ 2^{−10}.
  - Run conditional expectations on Ψ = Φ + 2·Coll, which has E[Ψ] ≤ 373/336 + 2^{−9} < 1.1121 < 64/57.
  - The output seed has Ψ < 64/57. Hence 2·Coll < 1.13, so Coll = 0 because Coll is an integer, and Φ < 64/57, so δ > 7/8.
  - Coll is a CNT query of arity 2 within one block, with the seed as auxiliary bits.
- **Consequence.** The address idx_i := t_i is injective on F_i, its width is k = c = O(L/m), and the lookup boundary is β = 4mk = Θ(L).
  - Encoding density, x-coordinates and parity bits are no longer needed.
- **Generation.** D + D = G, so U = ∪F_i generates G.
- **Enumeration** of F_i and **2m-term decomposition** of any target use prefix pinning, exactly as in LZR Thm 3.1.

**(c) Stage II for a relation lattice.** This is the core generalisation.
- Index U = {A_1, …, A_N} and let φ : Z^N → G, e_j ↦ A_j. Then L_U = ker φ has index n.
- Maintain a full-rank lattice L' with nZ^N ⊆ L' ⊆ L_U. Initialise it with nZ^N and the N consistency vectors e_j − cnt(U^{(j)}), where U^{(j)} is the canonical 2m-term decomposition of A_j.
- **Loop.**
  - If det L' = n, stop: L' = L_U, because L' ⊆ L_U has the same index.
  - Otherwise compute the Smith normal form Z^N/L' ≅ ⊕_{i≤N} Z/d_i, with coordinate maps ψ_i : Z^N → Z/d_i, where d_i | n.
  - For each pair (i, j), query
    Z_{i,j} = Σ_{(X,Y): val Y = val X + A_j} Q_i(Λ_{ψ_i}(Y) − Λ_{ψ_i}(X)),
    where Q_i(X) = ∏_{t=−w−1}^{w} (X − ψ_i(e_j) − t d_i)².
    - This is LZR (4.3) with modulus d_i and target ψ_i(e_j) in place of 1.
    - It is nonnegative and vanishes exactly on ≡ ψ_i(e_j) (mod d_i).
    - Its labels are (1+z)^{±ψ_i(e_A)}, and its degree is 4w+6.
  - If some Z_{i,j} > 0, pin the O(mL) tuple bits to extract a violating (X*, Y*). Add v = cnt(Y*) − cnt(X*) − e_j ∈ L_U \ L'.
  - The index [Z^N : L'] at least halves, so there are ≤ N log₂ n iterations.

**Lemma (lattice certification; generalises LZR Prop 4.1).** Suppose L' ⊆ L_U contains the consistency vectors, and suppose every pair with val Y = val X + A_j satisfies π(cnt Y − cnt X) = π(e_j), where π : Z^N → Z^N/L' and j ranges over [N]. Then L' = L_U.

*Proof.*
1. Every g ∈ G has a block-respecting representation (Stage I).
2. Define f(g) = π(cnt X) for any representation X of g. It is well defined: if val X = val X' = g, take a representation Y of g + A_1. Then π(Y) − π(X) = π(e_1) = π(Y) − π(X').
3. Hence f(g + A_j) = f(g) + π(e_j) for all g and j.
4. Consistency gives f(A_j) = π(cnt U^{(j)}) = π(e_j). With f(A_j) = f(0) + π(e_j), this gives f(0) = 0.
5. The A_j generate the finite group G, so every v ∈ Z^N_{≥0} satisfies f(φ(v)) = π(v) (induction on |v|₁).
6. For v ∈ L_U write v = v⁺ − v⁻. Then φ(v⁺) = φ(v⁻), so π(v⁺) = π(v⁻) and π(v) = 0.
7. So L_U ⊆ L', and therefore L' = L_U. ∎

After the loop, π(v) = 0 holds in Z^N/L' for every tested pair. So when the loop ends with no violation, the lemma applies. (The det test is only a shortcut.)

**(d)** The Smith normal form of L_U gives G ≅ ⊕ Z/n_i. The basis elements are φ of the columns of the unimodular transform. They are computed by multiplications; no exponentiation chains are needed beyond poly(N, L) group operations, done with double-and-add.

**(e)** Decompose P and Q into vectors p and q (Stage I). Then solve x·ψ(p) ≡ ψ(q) in ⊕ Z/n_i. This is a system of univariate congruences. Use gcd tests for membership and CRT for x modulo ord(P).

**Query arity.** Stage II pairs have 4m slots plus one hard-wired constant, so the arity is 4m+1. Stage I uses ≤ 2m slots plus seeds.

**Counts.**
- Iterations: N log n = 2^{O(L/m)}.
- Queries per iteration: N² + O(mL).
- Smith normal form: poly(N, log n) (Kannan–Bachem, Storjohann). ∎

**Routine checks still owed.**
- E[Coll] uses independence of the tag seed from the membership seed. ✔
- c and α ≠ 0 enter H_η, the prefix-completion count. ✔
- Q_i range: |Λ_ψ(Y) − Λ_ψ(X)| ≤ w(d_i − 1), so t ∈ [−w−1, w] suffices. ✔

### Why this is the boundary (Theorem D1-C below)

Shoup and Nechaev's Ω(√p_max) counts *group operations*. A single CNT_k query aggregates n^{k−1}·(seed space) relations, so the lower bound does not apply. In the structured generic-group model of Corrigan-Gibbs–Henzinger–Wu (ePrint 2026/384), the bound Ω(min(√q, 1/δ)) is in terms of the fraction δ of elements whose structure the algorithm exploits. A CNT query touches *every* element, so δ = 1.

---

## Theorem D1-A (deterministic structure and DLOG for linear-wire groups; conditional on D.1 and T4.3)

**Statement.** Let (G, ι, L) be a linear-wire encoded finite abelian group (W = O(L)). Then (a)–(e) of D1-B are computable by a uniform deterministic multitape TM in time

  2^{O(L/√(log log L))},

with space 2^{O(L/(log L)^{1/4})}. No randomness and no GRH are used.

**Status.** Sketch, with the gap named. Confidence 0.55. That is ≈ 0.9 for the reduction times ≈ 0.6 for T4.3.

**Proof.** Instantiate every CNT query of D1-B, with m = ⌈(log L)^{1/4}⌉, by a BTN.
- **Stage I queries.**
  - The network has O(m) group-law gadgets, O(m) GF(2^{L'}) multiply-and-compare gadgets for h_i and t_i, and seed wires.
  - Edges: O(mW + mL) = O(mL). Degree: O(L^{9/10}).
  - D.1 gives 2^{O(mL/√log L)} = 2^{O(L/(log L)^{1/4})}.
  - GF(2^{L'}) multiplication with O(L') wires: one level of Schönhage's ternary FFT over F_2[y]/(y^{2·3^j}+y^{3^j}+1), split into two layers exactly as LZR Lemma 2.3. Data volume O(L'), vertex degree O(L'^{3/4}). (Sketch; same data-flow as Lemma 2.3.)
- **Stage II queries** have exactly the shape of LZR's N_y:
  - a core with S = Θ(mL) edges and degree O(L^{9/10});
  - 4m lookup vertices of degree k = c = O(L/m);
  - β = 4mk = Θ(L) open boundary edges on distinct degree-2 vertices.
  - T4.3 gives 2^{O(L/√log log L)} per query.
  - The tables are mod d_i rather than mod M_lab, and the filter degree goes from 8m+2 to 8m+6. Neither changes T4.3's hypotheses: ℓ = O(m) and P0 = Θ(mL).
- **Total.** Multiply the query count 2^{O(L/m)} by the per-query cost. ∎

**Named gaps.**
- **G1:** T4.3 / LZR §5 (Lemma 5.1(ii) with open boundary). Inherited.
- **G2:** the ternary-FFT wire lemma for GF(2^{L'}). Sketch, high confidence 0.85. D2's chunked-F_p hash avoids it altogether.

---

## Dependencies

| Result | D.1 | T4.3 | GRH | Randomness |
|---|---|---|---|---|
| D1-B | no | no | no | no |
| D1-A, Cor 1–4 | yes | yes | no | no |
| Cor 4, h(Δ) only | yes | no | no | no |
