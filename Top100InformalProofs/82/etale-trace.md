# Trace tensors and reconstruction of étale algebras

The reconstruction works over the base field and uses the finite étale algebra trace pairing.

## 1. Trace tensors of étale algebras

Let E be an étale F-algebra of dimension n. Its trace tensor is the trilinear form

  t_E(x,y,z) = Tr_{E/F}(xyz), an element of E*⊗E*⊗E* ≅ F^n⊗F^n⊗F^n.

The action is (A,B,C)·t = t(A^{-1}·, B^{-1}·, C^{-1}·). In a basis, the coordinates are integers whenever the structure constants are.

**Theorem 1.** Let E, E' be étale F-algebras of the same dimension n, with F any field. Then t_E ≅_F t_{E'} ⟺ E ≅ E' as F-algebras.

*Proof.*

(⇐) An algebra isomorphism φ: E → E' preserves traces, so (φ,φ,φ) carries t_E to t_{E'}.

(⇒) Suppose t_{E'}(Ax,By,Cz) = t_E(x,y,z) for all x, y, z, with A, B, C: E → E' F-linear and invertible.

1. **Rank-one decomposition.** Let Λ = Hom_{F-alg}(E, F̄), which has n elements, and similarly Λ' for E'. Extended F̄-linearly, Λ is a basis of (E⊗F̄)*, and t_E = Σ_{λ∈Λ} λ⊗λ⊗λ. (The trace of an étale algebra is the sum of its embeddings.)
2. **Slice space.** The slice space S_E = {t_E(·,·,z) : z ∈ E⊗F̄} equals {Σ μ_λ λ⊗λ : μ ∈ F̄^Λ}, because z ↦ (λ(z))_λ is bijective. Since Λ is a basis, the rank of Σ μ_λ λ⊗λ is #{λ : μ_λ ≠ 0}. So the rank-one elements of S_E are exactly the nonzero multiples of the n forms λ⊗λ.
3. **Transport of slices.** The hypothesis says t_E(·,·,z) = t_{E'}(·,·,Cz)∘(A×B). Since C is bijective, the map β ↦ β∘(A×B) is a rank-preserving bijection S_{E'} → S_E.
4. **Matching of embeddings.** Hence for every λ ∈ Λ there is a unique λ' = π(λ) ∈ Λ' with λ'∘A ∈ F̄^×·λ, and π: Λ → Λ' is a bijection.
5. **Galois equivariance.** Let σ ∈ Gal(F̄/F). Since A is F-linear, applying σ to λ'∘A = aλ gives (σ∘λ')∘A = σ(a)(σ∘λ). So π(σ∘λ) = σ∘π(λ), i.e. π is a Gal_F-equivariant bijection.
6. **Conclusion.** By Grothendieck's Galois theory, finite étale F-algebras are anti-equivalent to finite continuous Gal_F-sets via E ↦ Hom(E, F̄). Therefore E ≅ E'. ∎

**Cohomological reading.** Over F̄, t_E is the unit tensor ⟨n⟩. Its stabiliser is a form of T₂ ⋊ S_n, where T₂ = {(a,b,c) diagonal : a_i b_i c_i = 1}. Over F, G_{t_E} = T₂(E) ⋊ Aut(E), where:
- T₂(E) ≅ (R_{E/F}G_m)² is a quasi-trivial torus, so H¹ = 0 by Hilbert 90 and Shapiro;
- Aut(E) is the finite étale automorphism scheme (the twisted S_n).

Theorem 1 is the statement H¹(F, G_{t_E}) = H¹(F, Aut E) = {forms of E}. The proof above avoids cohomology and works for every F.

**Corollary 1.1 (field-uniform reduction).** E ↦ t_E is a field-uniform, ℤ-defined reduction from étale-algebra isomorphism (number-field isomorphism) to 3-TI. It is correct simultaneously over Q, R and every Q_p.

## 2. Hasse failures: explicit pairs

### Theorem 2 (6×6×6 pair, entries in {0,1,13,17,221})

Let:
- K = Q(√13, √17), with quadratic subfields K₁ = Q(√13), K₂ = Q(√17), K₃ = Q(√221);
- E = K × Q × Q and E' = K₁ × K₂ × K₃, both of dimension 6.

Then t_E ≅_{Q_v} t_{E'} for every place v of Q, but t_E ≇_Q t_{E'}.

**The tensors explicitly.** Both are block-diagonal, and each block is rescaled by an invertible block-scalar in GL. The rescaling is allowed over every field, so it changes no isomorphism question.

*T = (¼ t_K) ⊕ ⟨1⟩ ⊕ ⟨1⟩.*
- Index the K-block by the subsets ∅, {u}, {w}, {u,w}, i.e. the basis 1, √13, √17, √221.
- The entry (S₁,S₂,S₃) is nonzero only when S₁ Δ S₂ Δ S₃ = ∅. Then it equals 13^{c_u/2}·17^{c_w/2}, where c_u is the number of S_i containing u (and similarly c_w).
- The nonzero entries are:
  - (∅,∅,∅) = 1;
  - the three permutations of (∅,u,u) equal 13;
  - those of (∅,w,w) equal 17;
  - those of (∅,uw,uw) equal 221;
  - all six permutations of (u,w,uw) equal 221.
- The two ⟨1⟩ blocks are single entries 1 at positions (5,5,5) and (6,6,6).

*T' = ⊕_{d∈{13,17,221}} B_d.* Each B_d is the 2×2×2 block with (0,0,0) = 1, (0,1,1) = (1,0,1) = (1,1,0) = d, and all other entries 0. This is ½ t_{Q(√d)} in the basis 1, √d.

*Proof.* By Theorem 1 it suffices to show:
- (a) E⊗Q_v ≅ E'⊗Q_v for all v;
- (b) E ≇ E'.

(b) An étale algebra is uniquely a product of fields. The factor multisets {K, Q, Q} and {K₁, K₂, K₃} differ.

(a) **Key fact:** at every place v, at least one of 13, 17, 221 is a square in Q_v.
- v = ∞: all three are positive.
- v = 2: 17 ≡ 1 (mod 8).
- v = 13: 17 ≡ 4 = 2² (mod 13), and Hensel applies.
- v = 17: 13 ≡ 64 = 8² (mod 17).
- Odd p ∉ {13, 17}: the Legendre symbols satisfy (13/p)(17/p) = (221/p), and they are not all −1.

**Case 1: all three are squares in Q_v.** Both algebras are Q_v⁶.

**Case 2: exactly one is a square.** Say d₀ is a square and d₁, d₂ are not. Then d₁/d₂ = d₀·(square) is a square, so Q_v(√d₁) = Q_v(√d₂) =: L, a quadratic field.
- K⊗Q_v = Q_v(√d₀, √d₁)-algebra ≅ L×L, so E_v ≅ L×L×Q_v×Q_v.
- E'_v ≅ Q_v×Q_v×L×L.

These are the only cases, because "exactly two squares" forces the third (a product of two squares) to be a square. ∎

**Remark (where this comes from).** In Galois-set terms, with G = Gal(K/Q) = V₄ and A, B, C its subgroups of order 2, the two algebras correspond to:

  X = G/1 ⊔ pt ⊔ pt  and  X' = G/A ⊔ G/B ⊔ G/C.

- The two sets have the same permutation character.
- They are isomorphic as D-sets for every cyclic D ≤ G but not for D = G.
- So the pair is locally isomorphic exactly when every decomposition group is cyclic. That is the same condition under which the norm-one torus of K has Ш¹ = ℤ/2 (Tate; Cassels–Fröhlich Ex. 5.3).
- So this is the norm-torus phenomenon of HW-2, carried by a finite stabiliser instead of a torus.
- Degree 6 is the least degree of a pair of linearly equivalent non-isomorphic G-sets for V₄.

### Theorem 3 (8×8×8 field pair, Grunwald–Wang type)

Let K = Q(α) with α⁸ = 34, and L = Q(β) with β⁸ = 544 = 16·34. Define

  T_a[i,j,k] = a^{(i+j+k)/8} if 8 | i+j+k, and 0 otherwise  (0 ≤ i,j,k ≤ 7).

This is ⅛ t_{Q(a^{1/8})} in the power basis, since Tr(α^m) = 8a^{m/8} when 8 | m and 0 otherwise.

Then T₃₄ ≅_{Q_v} T₅₄₄ for all v, but T₃₄ ≇_Q T₅₄₄.

*Proof.* By Theorem 1 it suffices to compare the algebras.

1. **Both are fields.** x⁸ − 34 is Eisenstein at 2 (and at 17). x⁸ − 544 = x⁸ − 2⁵·17 is Eisenstein at 17. So both are irreducible and K, L are degree-8 fields.
2. **Odd p (Wang's lemma).** One of −1, 2, −2 is a square in Q_p.
   - If 2 = s², put y = s.
   - If −2 = s², put y = s.
   - If −1 = i², put y = 1+i, since (1+i)² = 2i and (2i)⁴ = 16.

   In every case y ∈ Q_p and y⁸ = 16. The substitution x ↦ yx gives Q_p[x]/(x⁸−544) ≅ Q_p[x]/(x⁸−34).
3. **v = ∞.** Take y = √2.
4. **v = 2.** Q₂[x]/(x⁸−34) = Q₂(α) is a totally ramified field of degree 8 (Eisenstein). It contains α⁴ = √34 = √2·√17, and √17 ∈ Q₂ since 17 ≡ 1 (mod 8). So c = √2 lies in Q₂(α).
   - (cα)⁸ = 16·34 = 544.
   - v(cα) = 1/2 + 1/8 = 5/8, so cα generates a totally ramified extension of degree divisible by 8.
   - Hence x ↦ cα gives Q₂[x]/(x⁸−544) ≅ Q₂(α).
5. **Globally.** K ≅ L would give θ ∈ K with θ⁸ = 544. Then c = θ/α ∈ K satisfies c⁸ = 16, so c² ∈ {±2, ±2i}. Hence K would contain one of √2, √−2, i.
   - K embeds in R, so √−2 and i are excluded.
   - If √2 ∈ K, then √17 = √34/√2 ∈ K. But 2 is totally ramified in K (Eisenstein), while Q(√17) is unramified at 2. Contradiction. ∎

This agrees with Komatsu's residue-class criterion: 34 ≡ 2 (mod 16), Kodai Math. J. 1 (1978). It is a sibling of the de Smit–Perlis example a ≡ −1 (mod 32). The local and global steps above were checked independently of those sources.
