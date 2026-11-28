# A conditional circuit lower bound for binary code equivalence

The result depends on the named unrefereed tagged lower bound. The Boolean encoding convention is part of the statement.

## Input labels
- **[OpenAI, Lean]** `OAI.LinearAlgebra.MatrixExponent.BatchDescent.hard`, i.e. `Tagged.Hard F` for every finite field F ([local reference omitted] definition in Tagged/Hard.lean:11).
  - It says: there is σ > 0 such that for all large w, every exact trivalent F-network computing tag_w has at least 2^w·w·w^σ vertices.
  - Here tag_w(x1, x2) = 1 iff the list x2 of 2^w rows (i, y) ∈ {0,1}^w × {0,1}^w is a permutation (List.Perm) of the indexed list {(j, x1_j) : j ∈ [2^w]}, where x1_j ∈ {0,1}^w (Tagged/Tags.lean:29, 108).
  - This is the "Tag / multiset-equality" form of oaM Thm 2.2, the matrix-multiplication-exponent paper (eldist R-D4 C3).
- **[ours]** The Boolean circuit → exact network compilation (eldist R-D1 §2, which is verbatim oaM Prop 2.4). A fan-in-2 circuit with s gates on n inputs becomes a trivalent network with at most 3s + n + 1 vertices computing the same 0/1 function exactly, over any field.
- **[classical]**
  - Permutation code equivalence (PCE) is GI-hard (Petrank–Roth 1997).
  - Code equivalence lies in the TI class (Grochow–Qiao). The reduction is polynomial, not linear, which matters below.

## Problem
PCE₂(k, M): the input is two k×M matrices G, H over F₂ (n = 2kM bits). Accept iff there are g ∈ GL_k(F₂) and π ∈ S_M with gG = H·P_π.

On full-rank inputs this is exactly permutation equivalence of the codes rowspace(G) and rowspace(H). Over F₂, permutation and monomial equivalence coincide.

Equivalently, with Cols(G) the multiset of columns: accept iff g_*Cols(G) = Cols(H) as multisets for some g ∈ GL_k.

## Theorem S1
Let k = 2w + 2 and M = 2^w + Φ(k), where Φ(k) = (k² + 3k)/2 = O(w²). There is σ > 0 (the OpenAI exponent for F₂) such that for all large w, every fan-in-2 Boolean circuit (any basis) that decides PCE₂(k, M) correctly on full-rank inputs has
  size ≥ c · n · (log n)^σ, with n = 2kM = (4 + o(1))·w·2^w.
The same bound holds for exact F_p-networks (mod-p counting nondeterministic circuits) for every prime p, since `hard` is proved for every finite field.

### Frame and encoding
Coordinates are 0..k−1. Let R = {x ∈ F₂^k : x₀ = x₁ = 1} be the data region.

The frame Fr is the multiset consisting of:
- e₀ with multiplicity 2;
- e_ℓ with multiplicity ℓ + 2, for ℓ = 1, …, k−1.

Then |Fr| = Φ(k). The multiplicities 2, 3, …, k+1 are pairwise distinct and ≠ 1. No frame point lies in R: e₀ has x₁ = 0, and e_ℓ has x₀ = 0 for ℓ ≥ 1.

The reduction is a projection: each input bit is copied to exactly one matrix entry, and every other entry is a constant. Given a Tag instance (x1, x2):
- the columns of G are d_j = (1, 1, bin(j), x1_j) for j ∈ [2^w], followed by Fr;
- the columns of H are (1, 1, i_r, y_r) for the rows r of x2, followed by Fr.

Both matrices have rank k, because Fr contains the basis e₀, …, e_{k−1}.

### Profile lemma
Let D_A ⊂ R be a set (no repeats) and D_B a multiset on R with |D_B| = |D_A|. If g ∈ GL_k(F₂) and g_*(D_A ⊎ Fr) = D_B ⊎ Fr, then g = id and D_A = D_B.

*Proof.* Let μ_A, μ_B be the multiplicity functions of the two sides. Because g is a bijection of F₂^k, μ_B ∘ g = μ_A, so the two sides have the same multiset of nonzero values (the "spectrum").
- Since frame points lie outside R, spec(μ_A) = {1^{|D_A|}} ⊎ {2, 3, …, k+1}.
- For the same reason, spec(μ_B) = spec(D_B) ⊎ {2, 3, …, k+1}.

Hence spec(D_B) = {1^{|D_A|}}, so D_B has no repeats.

Now μ_A and μ_B each take the value 2 at exactly one point, namely e₀. So g(e₀) = e₀. Likewise the value ℓ+2 is taken only at e_ℓ, so g(e_ℓ) = e_ℓ. These k points form a basis, so g = id, and therefore D_A = D_B. ∎

### Correctness
- Let D_A = {d_j}. These are distinct, since their index fields bin(j) differ. Let D_B be the multiset of rows of x2.
- tag(x1, x2) = 1 ⟺ D_A = D_B as multisets, by the definition of List.Perm.
- (⇒) If D_A = D_B, take g = id and π matching equal columns.
- (⇐) If PCE accepts, the profile lemma gives D_A = D_B.

### Size transfer
Suppose a circuit for PCE₂(k, M) has s gates.
1. Compose it with the projection. Constants become arity-1 tables, and no Tag input is used twice, so no copy vertices are needed.
2. Compile as in R-D1. The result is an exact F-network for tag_w with at most 3s + O(n) vertices.
3. `hard` gives 3s + O(n) ≥ 2^w·w·w^σ.
4. Since n = Θ(w·2^w) and log n = Θ(w), this gives s ≥ c·n·(log n)^σ − O(n). ∎

## Corollaries
1. **Every finite field F_q** (permutation equivalence). The same proof works: g permutes F_q^k and fixes the frame basis, so g = id.
   - Monomial equivalence over F_q, q > 2: work with projective points. Add the frame point u = e₀ + e₂ + … + e_{k−1} with multiplicity k+2; then g is diagonal with g = diag(λ, μ, λ, …, λ). The data region forces μ = λ, since the images of data points must land in R.
   - Sketch only; not K3-checked.
2. **Multi-hypergraph isomorphism.** Vertex set [k], k = 2w+2; hyperedges are given as characteristic vectors (n = 2kM bits); multi-edges are allowed. The same profile lemma applies with S_k in place of GL_k. So the same Ω(n(log n)^σ) bound holds.
3. **Canonization (the Fortnow–Grochow lattice at circuit scale).** Let a size-s circuit compute a complete invariant f, i.e. f(G) = f(H) ⟺ G ~ H on full-rank inputs (a canonical form is a special case). Then two copies plus an equality test decide PCE with at most 4s + 2n gates. So s = Ω(n(log n)^σ).
   - CF and Ker get the same bound; there is no separation.
   - Randomized promise version: on the image of the reduction, λ-free fingerprinting decides PCE with O(n log log n) randomized gates. This is the det-vs-rand gap of eldist R-D4 C3, transported, not new.
4. **Regime.** The bound lives at k = Θ(log M). There PCE is solvable by brute force over GL_k in M^{O(log M)} time, which is quasi-polynomial in n. So the complexity of this slice is between n(log n)^σ (circuits) and n^{O(log log n)}.
