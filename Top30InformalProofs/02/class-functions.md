# Noncommutative class-function polynomials

The hardness conclusions inherit the stated unrefereed inputs and circuit-model assumptions.

## Setting
- Let K be any field and f: S_N → K a class function, i.e. a function of the cycle type.
- The row-ordered nc permutation sum is P_f := Σ_π f(type π) · x_{1π(1)} x_{2π(2)} ⋯ x_{Nπ(N)} in K⟨x_{ij}⟩.
- Special cases:
  - Perm (f ≡ 1) and Det (f = sgn);
  - every immanant Imm_λ (f = χ_λ);
  - per_L, where f is the indicator that all cycle lengths lie in L: Hamiltonian cycles HC_N (L = {N}), derangements (L = ℕ∖{1}), and fpf involutions (L = {2});
  - our char-2 families P_f (C47), O_n, and per_{ℕ∖1}.
- C̲ is Liu's border nc circuit size over K̄.
- D_a := Σ_{w∈{0,1}^a} z_w z_w. Its four blocks have coefficient tensor C_{a/2}.
- mov(ρ) = N − m_1(ρ) is the number of moved points. μ(f) := max{mov ρ : f(ρ) ≠ 0}.

## Theorem S1 (nc class-function classification, every field)
For every field K and every class function f on S_N with μ = μ(f):

  μ/32 − O(√(μ log μ)) ≤ log₂(C̲(P_f)+1) ≤ log₂ ncABP(P_f) ≤ O(μ log N).

So log C̲_nc(P_f) = Θ̃(μ(f)): the nc complexity of a class-function permanent is fixed, up to a log N factor in the exponent, by how many points its support moves. This holds in every characteristic, with constants independent of K and f. Constants per family:

| family | lower bound on log₂ C̲ (minus O(√(N log N))) |
|---|---|
| HC_N, every field | N/6 |
| every immanant Imm_λ, λ ⊢ N, every field | N/6 |
| per_L, L ∋ ℓ ≥ 3 | ≥ N/10 (derangements: N/6) |
| per_L, {1,2} ⊆ L | N/6 |
| per_{{2}} (fpf involutions) | N/8 |
| nc hafnian (product ordered by smaller endpoint) | N/8 |

**Corollary (nc per_L dichotomy).** nc per_L is 2^{Ω(N)} over every field iff L ≠ {1}. (If L = {1}, P is a single monomial.)

**Corollary (char 2).** Over F_2 the following have poly-size commutative ABPs (our C10, C47, C-V3-b, C23, CLOSE-V3 cofinite boundary) but need nc circuits of size 2^{Ω(N)}:
- haf = Pf;
- involution sums;
- per_{ℕ∖1};
- per*;
- loop hafnian.

The commutative char-2 collapse is a purely commutative phenomenon. Every VNP-complete family in our permutation-based dichotomies, and also every VP-side one, becomes nc-exponential with an explicit linear exponent.

**Corollary (immanants).** In the commutative setting, immanants run from VP (bounded b(λ), det) to VNP-complete. In the nc setting every immanant is 2^{N/6−o(N)}, uniformly in λ and K.

## Proof

**Step 0 (projection).** Substitute each x_{rs} by 0, a scalar, or a scalar times z0 or z1. This is a K-algebra map K⟨x⟩ → K̄⟨z0,z1⟩. It sends exact or border circuits of size s to circuits of size ≤ s, so C̲(image) ≤ C̲(P_f). Rows are labels: we choose the "emitting" rows i_1 < … < i_a < i'_1 < … < i'_a in row order. Helper rows get scalar entries, so they occupy no word position.

**Step 1 (type-preserving gadgets).** Each gadget has exactly two local completions. Both completions have the same cycle type, and they emit (z0 at i, z0 at i') and (z1 at i, z1 at i') respectively. C++ enumeration of all covers confirms this (gadgets.cpp, a ≤ 3, ALL PASS).
- **A, (2,1)** on rows {i, i', h}:
  - entries (i,i)=z0, (i',h)=z0, (h,i')=1, (i,i')=z1, (i',i)=z1, (h,h)=1;
  - the only covers are (i)(i' h) and (i i')(h).
- **B, (3)** on rows {i, i', h}:
  - entries (i,i')=z0, (i',h)=z0, (h,i)=1, (i,h)=z1, (h,i')=1, (i',i)=z1;
  - the support is the off-diagonal of a 3×3 block, so the only covers are its two 3-cycles.
- **C, in-cycle.** A cycle of length ℓ hosts ⌊ℓ/3⌋ gadgets plus ℓ mod 3 scalar path rows.
  - Gadget j has rows (i, i', h). Its successor column is nxt = the next gadget's i, or a scalar row.
  - Entries: (i,i')=z0, (i',h)=z0, (h,nxt)=1, (i,h)=z1, (h,i')=1, (i',nxt)=z1.
  - The row–column graph is a disjoint union of 6-cycles, one per gadget, so there are exactly 2^g covers. Each cover is a single ℓ-cycle. This was checked for ℓ = 3..11.
- **D, (2,2)/(4)** on rows {i, i', h1, h2}:
  - entries (i,h1)=z0, (i',h2)=z0, (i,h2)=z1, (i',h1)=z1, (h1,i)=(h2,i')=(h1,i')=(h2,i)=1;
  - each bit has exactly two covers, of types (2,2) and (4), and mixed bits are impossible;
  - the per-word multiset of types is identical across words (C++ check).
- **Padding.** Any fixed permutation matrix μ with scalar entries.

If every gadget used is of type A, B or C and the base type is ρ, then the substitution gives P_f(X') = f(ρ)·D_a.

If D-gadgets are used, put F(t) := f(ρ with t pairs of 2-cycles merged into 4-cycles). Each word then has coefficient Σ_t C(a,t)F(t). Choose t0 = max{t ≤ a : F(t) ≠ 0}, and realise t0 merges as fixed 4-cycles. The remaining a − t0 D-gadgets then give coefficient F(t0) ≠ 0 on every word.

**Step 2 (capacity).** Take ρ ∈ supp f with mov ρ = μ. Write L3 = Σ_{ℓ≥3} ℓ·m_ℓ, so that μ = 2m_2 + L3. Note ⌊ℓ/3⌋ ≥ ℓ/5 for ℓ ≥ 3.
- **m_1 ≥ m_2.** A + C gadgets give a ≥ L3/5 + m_2 ≥ μ/5.
- **m_1 < m_2 and L3 ≥ μ/2.** C gadgets give a ≥ μ/10.
- **Otherwise m_2 ≥ μ/4.** D gadgets on ⌊m_2/2⌋ pairs. Either a − t0 ≥ ⌊m_2/2⌋/2, or the type ρ' = ρ + t0 merges lies in supp f and has ≥ t0 4-cycles, each hosting one C gadget. Either way a ≥ μ/16 − 1.

So f has some type ρ* with P_f ≥_proj c·D_a, where c ≠ 0 and a ≥ μ/16 − 1.

**Step 3 (Liu + OpenAI).** Liu Thm 1.1's proof applies Lemma 2.1 to D_{2r}, whose four-block tensor is C_r. The planar hypothesis is discharged over every field by OpenAI `HasSpectralFlat.plane` plus our glue (audit-L2-glue.md, PASS). This gives log₂(C̲(D_a)+1) ≥ a/2 − O(√(a log a)). With a ≥ μ/16 − 1 we get the lower bound.

**Step 4 (upper bound).** An nc ABP reads rows 1..N. Its state is the partial map π restricted to the moved rows read so far, together with the set of columns used. There are ≤ N^{2μ+O(1)} states. At the end it checks bijectivity and multiplies by f(type). Size N^{O(μ)}, any field.

**Explicit families.**
- **Immanants.** Let ρ_λ = (h_11, …, h_dd), the principal hook lengths. By Murnaghan–Nakayama, χ_λ(ρ_λ) = ±1: at each step the unique rim hook of maximal length is the outer rim. C++ check: all 11731 partitions with N ≤ 26 give ±1. Its gadget capacity is Σ⌊h_ii/3⌋ ≥ (N − 2d)/3 ≥ (N − 2√N)/3. This gives N/6.
- **HC_N.** Gadget C on the N-cycle, a = ⌊N/3⌋.
- **Hafnian.** Vertices i, i' and helpers h1, h2 placed after all i, i'. Edges {i,h1}=z0, {i',h2}=z0, {i,h2}=z1, {i',h1}=z1. Words are read by min endpoint. There are exactly 2^a matchings and the words are w_S w_S (C++ check, a ≤ 3).
- **per\*, all-matchings, loop hafnian.** Take the degree-N homogeneous component (O(d²) overhead, Liu §3), then use Perm or Haf.

## Inputs
- **OpenAI (treated as proved):** `HasSpectralFlat K 2` (`HasSpectralFlat.plane`, every field).
- **Liu (2611.00994):** Lemma 2.1 (the cost test for D_{2r}), the closure/border handling, and the prime-field invariance of border size. The HWY Lemma 2.3 "D_n from Perm_{2n}" is the prior special case of gadget A for f ≡ 1.
- **Ours:**
  - the planar glue (audit PASS);
  - the type-preserving gadget calculus A–D with the t0 trick;
  - the capacity bound μ/16;
  - the principal-hook immanant embedding;
  - the hafnian gadget;
  - the N^{O(μ)} ABP upper bound;
  - the char-2 consequences for our families.
