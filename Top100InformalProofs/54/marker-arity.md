# Tensor and direct-sum marker arity

The halving law and the exact finite-field statements are the audited parts.

## 0. Definitions

U = F^n. A **mixed tensor space** is M = U^{⊗a} ⊗ U*^{⊗b}, of arity a+b. A **marker datum** is a finite list of:
- tensors t_i in mixed tensor spaces;
- subspaces W_j ⊆ M_{j1} ⊕ … ⊕ M_{jr}, direct sums of mixed tensor spaces, where the arity of W_j is the maximum arity of its summands.

The arities are:
- ar_T(G): the least r such that G = Stab_{GL(U)}(tensors of arity ≤ r), and ∞ if no such r exists;
- ar_hom(G): the same, with tensors and subspaces of a single M allowed (the 11-14 definition);
- ar_⊕(G): the same, with tensors and direct-sum subspaces allowed.

For G ≤ H, κ(G,H) is the least arity of a G-invariant tensor that is not H-invariant.

Multi-sort versions (U, V, W, or the six GA slot sorts) count legs per sort.

---

## 1. Theorem H (halving law)

**H1 (graph lemma, any field, any G).** Let t ∈ M_A ⊗ M_B with arity |A|+|B|, and let φ_t: M_A* → M_B be the associated map. Then
  Stab_{GL(U)}(graph φ_t) = Stab(t),
and graph φ_t ⊆ M_A* ⊕ M_B has arity max(|A|,|B|).

*Proof.* graph φ is g-stable ⟺ g∘φ∘g⁻¹ = φ ⟺ g·t = t, because t ↦ φ_t is a GL-isomorphism M_A⊗M_B ≅ Hom(M_A*, M_B). ∎

Splitting the legs evenly gives **ar_⊕(G) ≤ ⌈ar_T(G)/2⌉**.

**H2 (doubling lemma; char 0, G reductive, or any finite G in char ∤ |G|).** Let G ≤ H ≤ GL(U), and let W ⊆ M = ⊕M_j be G-stable of arity r with 2r < κ(G,H). Then W is H-stable.

*Proof.*
- Complete reducibility gives a G-equivariant projection P onto W.
- P lies in M*⊗M = ⊕ M_i*⊗M_j, whose components have arity ≤ 2r < κ.
- P is G-invariant, hence H-invariant, so W = im P is H-stable. ∎

**Theorem H.** For G reductive in char 0 with ar_T(G) < ∞ (always true by Chevalley, since a reductive group is observable), ar_⊕(G) = ⌈ar_T(G)/2⌉.

*Proof.*
- The upper bound is H1.
- For the lower bound, let k = ar_T(G) and H := Stab(all G-invariant tensors of arity < k). Then H ⊋ G and κ(G,H) ≥ k.
- Let a datum have ⊕-arity r ≤ ⌈k/2⌉−1, so 2r < k. Its tensors are H-invariant, and by H2 its subspaces are H-stable. So its stabiliser contains H ≠ G. ∎

**Values (char 0).**

| G | ar_T | ar_hom (11-14) | **ar_⊕** | witness |
|---|---|---|---|---|
| GL_n | 0 | 0 | 0 | — |
| parabolic, Borel | ∞ (non-reductive) | 1 | 1 | flag |
| O_n, Sp_{2m} | 2 | 2 | **1** | graph of q: U → U* |
| SL_n | n | n | **⌈n/2⌉** | graph Λ^kU → Λ^{n−k}U*, k = ⌊n/2⌋ |
| SO_n | n | n (odd), n/2 (even) | **⌈n/2⌉** | q plus the graph of the Hodge star |
| SL^{(k)} = {det ∈ μ_k} | nk | nk | **⌈nk/2⌉** | graph of Λ^{n/2}U⊗det^{(k−1)/2} ≅_SL Λ^{n/2}U*⊗det^{−(k−1)/2}, and similarly for n odd |
| SU_n | n | n | ≤ ⌈n/2⌉ | Hermitian form plus graph (lower bound not done) |

Notes on the table:
- SO_n uses FFT for SO: invariants of arity < n carry no ε, so κ(SO,O) = n.
- The 11-14 A2 claim "ar(SO_odd) = n even with subspace markers" holds only for homogeneous subspaces. Its proof ("−I preserves every subspace") fails on Λ^m ⊕ Λ^{m+1}.

**The dichotomy, restated.** Every solved TI_G has ar_⊕ ≤ 1 (a flag or the graph of a form). Every open one (SL, SO, SU, SL^{(k)}) has ar_⊕ ≥ ⌈n/2⌉. The halving does not touch complexity: graph markers live in sorts of dimension C(n,⌊n/2⌋) ≥ C(n,⌈n/3⌉), consistent with the volume optimum.

## 2. Theorem F (finite fields, exact)

Let q = p^e, m | q−1, m < q−1, and G_m = SL_n(F_q)·⟨diag(ζ_m,1,…,1)⟩ = {det ∈ μ_m}. This covers SL (m = 1). Let T be the diagonal torus and T_m = T ∩ G_m. Both have order prime to p, so every T_m-stable space splits into weight spaces.

**F1 (tensors).** ar_T(G_m) = n·m.

*Proof.*
- **Lower bound.** Let t be G_m-fixed. Then its weight vectors are T_m-fixed. Their weights w ∈ (Z/(q−1))^n have a character trivial on T_m, which means w ≡ c·(1,…,1) with m | c.
- If c ≢ 0, every coordinate satisfies |w_i| ≥ dist(c,(q−1)Z) ≥ m, because the nonzero elements of mZ/(q−1)Z lie in [m, q−1−m]. So the arity is ≥ Σ|w_i| ≥ nm.
- If c ≡ 0, the vector is T-fixed. Since GL = SL·T, t is GL-fixed.
- **Upper bound.** ε^{⊗m} ∈ (Λ^nU*)^{⊗m} has stabiliser {det^m = 1} = G_m. ∎

**F2 (subspaces).** ar_⊕(G_m) = ⌈nm/2⌉. In particular ar_⊕(SL_n(F_q)) = ⌈n/2⌉.

*Proof.*
- **Lower bound, step 1.** Let W be G_m-stable. Then W = ⊕_χ (W ∩ M_χ) over the T_m-isotypic parts.
- **Step 2.** Two T-weights w, w′ in the same T_m-class differ by c·1 with m | c. If c ≢ 0, then Σ|w_i| + Σ|w′_i| ≥ Σ dist(w_i − w′_i, (q−1)Z) ≥ nm.
- **Step 3.** If every summand has arity < nm/2, each T_m-isotypic part is T-isotypic, so T acts on it by scalars. Hence W is T-stable, so it is GL-stable.
- **Upper bound.** This is H1 applied to ε^{⊗m}, with the twisted Λ^j trick from §1 (over F_q, Λ^jU ≅ Λ^{n−j}U*⊗det). The stabiliser is {det^m = 1}. ∎

H2 is not needed here: it fails in the modular case, but the torus argument does not.

**[C++] fixdim.cpp** computes dim Fix of SL, of G_m and of GL on every U^{⊗a}⊗U*^{⊗b}. The first arity with Fix(G_m) ⊋ Fix(GL) equals nm in every case:
- n=2, q=7: m=1,2,3 give 2, 4, 6;
- n=2, q=13: m=1,2,3,4 give 2, 4, 6, 8, and m=6 shows no gap up to 9 (predicted 12);
- n=3, q=5: m=1,2 give 3, 6;
- n=3, q=7: m=1 gives 3, m=2 gives 6, and m=3 shows no gap up to 6 (predicted 9);
- n=4, q=5: m=1 gives 4.

**[C++] graph.cpp** checks the graph of Λ^kU → Λ^{n−k}U*, x ↦ ε(x∧·). In every case all transvections preserve it, and diag(w^j,1,…) preserves it iff w^j = 1, so Stab = SL_n(F_p). Cases (n,p,k): (2,5,1), (3,7,1), (3,7,2), (4,3,2), (4,5,2), (4,7,2), (5,11,2), (5,11,3), (6,7,3), (7,13,3), (8,5,4).
