# Selection polynomials for spin and Potts models

The projection and algorithm proofs concern the stated parameters. Claims of separation from VP inherit the named external inputs.

## 1. Definitions

Let F be a field. Fix q ≥ 2, a symmetric A ∈ F^{q×q} and a weight vector w ∈ F^q. The **selection polynomial** on K_n has one variable x_e for each pair e = uv:

  Z_{A,w,n}(x) = Σ_{σ:[n]→[q]} Π_v w_{σ(v)} Π_{e=uv} (1 + x_e A_{σ(u)σ(v)}) = Σ_{E'⊆E(K_n)} x^{E'} · Z_{A,w}([n], E').

So Z_{A,w,n} is the generating function, over all graphs on [n], of the weighted homomorphism count to (A, w). It lies in VNP⁰-type VNP over every field, by Valiant's criterion with σ encoded in Booleans.

- **Two-spin case:** q = 2, A = [[a,b],[b,c]], w = (w₀, w₁).
- **Potts case:** A = (a−b)I + bJ (q×q) and w = 1.

In the two-spin case, C2 is A = [[1,−1],[−1,1]] with w = 1, C17 is A = I with x ↦ x − 1, and C65 is a = c.

VP and VP-bar are taken over F. "∉ VP" means that no polynomial-size circuit family over F exists.

## 2. Theorems

**Theorem 1 (two-spin dichotomy, every field).** Z_{A,w} ∈ VP if and only if one of the following holds:
- (E1) w₀w₁ = 0. Then σ is constant and Z = w_s^n Π_e (1 + A_{ss} x_e).
- (E2) a = b = c. Then Z = (w₀+w₁)^n Π_e (1 + a x_e).
- (E3) char F = 2, a = c and w₀ = w₁. Then Z ≡ 0, because σ and its complement σ̄ have equal weight.

In every other case, Z_{A,w} ∉ VP and Z_{A,w} ∉ VP-bar, unconditionally given Hexagon.

**Theorem 2 (Potts dichotomy, every field).** Let q ≥ 2, A = (a−b)I + bJ and w = 1. Then Z ∈ VP if and only if:
- a = b, or
- char F = p > 0 and q mod p ∈ {0, 1}. Then Z ≡ 0, or Z = Π_e (1 + a x_e), respectively.

Otherwise Z ∉ VP and Z ∉ VP-bar. In particular:
- in characteristic 2, every Potts selection polynomial is in VP;
- in characteristic 0, Potts is hard for every q ≥ 2 whenever a ≠ b;
- in characteristic p, hardness depends only on q mod p.

**Corollaries.**
1. **Multivariate Tutte polynomial.** The multivariate Tutte (random-cluster) polynomial of K_n at a fixed q ∈ F, FK_n(q; v) = Σ_{E'} q^{k(E')} v^{E'}, is in VP iff q ∈ {0, 1}. This is proved for every q in the image of ℤ, that is, every q ∈ F_p in characteristic p and every integer q ≥ 2 in characteristic 0. The reason is that Z_Potts = Π(1+bx_e) · FK(q; (a−b)x/(1+bx)), and division elimination runs in both directions.
2. **A3 coordination (two-term exponential degree signatures).** Rank-one A = ααᵀ gives the degree-signature Holant polynomial Σ_{E'} x^{E'} Π_v f(deg v) with f(d) = w₀α₀^d + w₁α₁^d. Theorem 1 says it is hard unless α₀ = α₁ or w₀w₁ = 0, **in every characteristic, char 2 included**. This settles A3's open char-2 question for two-term exponential signatures.
3. **Explicit hard families over every field:**
   - Ising with an arbitrary external field;
   - the "covered-vertex" polynomial Σ_{E'} x^{E'} y^{#uncovered} at any constant y ≠ 1, with y = 0 giving the edge-cover polynomial (A = [[0,0],[0,1]]);
   - the signed cut enumerator (w = (1,−1), a = c, char ≠ 2).

   Every one of these is ∉ VP and ∉ VP-bar.

## 3. Toolkit

- **(T1) Field extension.** If F ⊆ F′, a circuit over F is a circuit over F′. So Z ∉ VP_{F′} implies Z ∉ VP_F, and likewise for VP-bar. All gadget constants below may therefore be chosen *generic* in an infinite extension F′ ⊇ F, for example F(t₁, t₂, …) or its algebraic closure, adjoining finitely many elements per n. Hardness is then proved over F′: per3 is VNP_{F′}-complete (C-V4-a) and VP_{F′} ≠ VNP_{F′} (Hexagon, every field, exact and border). This is why F₂, F₃ and F₅ cause no trouble here, whereas they block p-projection completeness of Cut².
- **(T2) Division elimination / truncation** (C2, C65 verbatim). Let a circuit of size s compute R(z) with R ≡ c(z)·f(z) mod (z)^{D+1}, where:
  - c is a product of polynomially many explicit power series with c(0) ≠ 0;
  - deg f ≤ D.

  Then f has a circuit of size poly(s, D). Multiply by the truncated inverse of c and take the homogeneous parts of degree ≤ D gate by gate; this works over any field. The same holds for multigraded truncation in two groups of variables. **Border:** run the construction over F′(ε); homogenisation in z treats ε as a constant.
- **(T3) Gadget calculus.** Use only K_M with each x_e set to:
  - 0, which gives the all-ones function J, that is, a non-edge;
  - a constant λ ∈ F′, which gives the pencil member B_λ = J + λA;
  - a power series φ(z) with φ(0) = λ₀, truncated.

  The value is Σ_σ Π_v w_{σv} Π_e M_e(σu, σv).
  - A *unary gadget* at v is a private subgraph hanging on v. It multiplies the weight of v by a vector u(σ_v).
  - Binary gadgets compose by matrix products, with the middle vertices' weights diag(w ∘ unaries) in between.

  When x occurs on one edge of the gadget, u(x) = P + xQ with P, Q ∈ F′². Write ρ(x) := u₁/u₀ = (P₁+xQ₁)/(P₀+xQ₀). This is a Möbius map, and it is non-constant iff det(P, Q) ≠ 0.

## 4. Proof of Theorem 1

The easy cases (E1)–(E3) are immediate. For the rest, assume w₀w₁ ≠ 0, not a = b = c, and not (E3).

**Lemma 1 (a variable unary or a pin).** One of the following holds:
- (i) Some unary gadget has det(P, Q) ≠ 0.
- (ii) "Symmetric case": a = c ≠ b and w₀ = ±w₁ with char F ≠ 2. Then pinning one vertex g₀ to spin 0 costs only the factor 2: for every network of N vertices, with N even when w₀ = −w₁, the full sum is 2 × (the sum with σ(g₀) = 0). In this case the edge v–g₀ with x is a unary gadget with u(x) = (1 + xa, 1 + xb), and det = a − b ≠ 0.

*Proof.* Write W = w₀ + w₁ and g = Aw.

- **(a) Pendant** v–(J+xA)–p. Here u(x) = W·(1,1) + x·g, so det = W(g₁ − g₀). This works unless W = 0 or g₀ = g₁.
- **(b) Balanced case: W ≠ 0, g₀ = g₁,** that is, w₀(a−b) = w₁(c−b) =: κ.
  - If κ = 0, then a = b = c, which is excluded.
  - If a = c, then w₀ = w₁. This is case (ii), or (E3) in characteristic 2.
  - Otherwise a ≠ c, and hence w₀ ≠ w₁. Take the triangle v, p, r with edges J + xA, J + μA, J + νA, and write A = bJ + D with D = diag(a−b, c−b).
    - Expand every edge as (1+x_i b)J + x_i D. This is an FK-type expansion, and D forces equal spins on the edges it selects.
    - Only the term in which all three D's are selected depends on σ_v. Since w_s d_s = κ, that term is xμν·d_s³ w_s² = xμν κ³/w_s.
    - Hence u_s = C(x) + xμνκ³/w_s with C independent of s, and det = C₀(μ, ν) · μνκ³ (1/w₁ − 1/w₀).
    - C₀(0, 0) = W² ≠ 0, so det ≠ 0 for generic μ, ν ∈ F′.
- **(c) W = 0, char ≠ 2.** Normalise w = (1, −1).
  - Pendant-of-pendant v–(J+xA)–p–(B)–r, with B → A generic. It gives u = (wᵀAw)·(1,1) + x·A(w∘g), where wᵀAw = a − 2b + c.
  - A(w∘g) ∝ (1,1) iff (a − c)(a + c − 2b) = 0.
  - So if a ≠ c and a + c ≠ 2b, then det ≠ 0.
  - If a + c = 2b and a ≠ c, write a = b + δ and c = b − δ. The triangle (J+xA, A, A) gives P = δ²(1,1) and Q = δ²(3b+δ, 3b−δ), so det = −2δ⁵ ≠ 0.
  - If a = c, we are in case (ii) with w₀ = −w₁.
- **(d) W = 0, char 2,** that is, w₀ = w₁ = 1.
  - The pendant-of-pendant gives Σ_t w_t g_t = a + c, and A g has coordinates differing by (a − c)².
  - So det ≠ 0 if a ≠ c. If a = c, we are in (E3).
- **Generic replacement.** Every "A" edge inside a gadget is replaced by J + λA with λ generic. The determinant is a polynomial in 1/λ that is non-zero at 1/λ = 0, so it stays non-zero. ∎

**Lemma 2 (all unaries).** Given (i) or (ii), every constant ratio r ∈ F′^× is realised by setting x to a constant: ρ is a bijection of P¹(F′).

Moreover, for any constant r_c and a fresh variable z, x(z) := ρ^{−1}(r_c(1+z)) is a power series in z, provided r_c ≠ ρ(∞). If r_c = ρ(∞), split r_c across two gadgets. The prefactor u₀(x(z)) is an invertible series, since P and Q are independent. ∎

**Lemma 3 (NAND up to diagonal scaling).** Take λ ∈ F′ generic and B = B_λ = [[a′,b′],[b′,c′]]. Let the middle vertex m carry total unary w∘u ∝ (c′², −b′²), which Lemma 2 allows. Then

  B·diag(c′², −b′²)·B = [[a′²c′² − b′⁴, b′c′(a′c′ − b′²)], [b′c′(a′c′ − b′²), 0]] = α·diag(1, s)·NAND·diag(1, s),

with NAND = [[1,1],[1,0]] and s = b′c′(a′c′ − b′²)/α.

The entries are non-zero for generic λ, for the following reasons:
- b′ = 1 + λb and c′ = 1 + λc are non-zero.
- a′c′ − b′² = λ(a + c − 2b) + λ²(ac − b²) is not identically 0 unless a = b = c, in every characteristic. In characteristic 2 the conditions read a = c and b² = a², hence a = b.
- a′c′ + b′² has constant term 2 when char ≠ 2, and equals a′c′ − b′² when char = 2. ∎

Each NAND edge contributes the ratio s to each endpoint and the scalar α globally. Corrections come from Lemma 2.

**Assembly.**
- Let G_N be the C41 graph, so that IP(G_N; T, −1) = per3_N(T). Its triple vertices have weight T_{rab} and its 3N pendants have weight −1.
- Realise G_N inside K_M with M = poly(N):
  - every edge of G_N becomes a NAND 2-path (Lemma 3), with its middle unary set by a constant gadget;
  - a vertex v of G_N-degree k receives one constant gadget with ratio (w₀/w₁)·s^{−k}·(−1) if v is a pendant;
  - a triple vertex receives the variable gadget with ratio (w₀/w₁)·s^{−k}·(1 + z_{rab}).
  - In case (ii), all gadgets are edges to the pinned g₀. If w₀ = −w₁ and M is odd, add one constant pendant to fix the parity, and correct its unary.
- The circuit for Z_{A,w,M} then computes c(z) · per3_N(1 + z) modulo degree N + 1, where:
  - c is a product of explicit invertible series (the u₀ prefactors, the NAND scalars α, the w₀ factors, and the factor 2 in case (ii));
  - per3_N(1+z) is per3_N evaluated at T = 1 + z.
- By (T2), per3_N(1+z), and hence per3_N(T) after z := T − 1, has a circuit of polynomial size over F′. That contradicts Hexagon together with C-V4-a over F′. Border version: by (T2). ∎

## 5. Proof of Theorem 2

**Easy side.** FK expansion gives Z = Π_e (1+bx_e) · Σ_{E'} q^{k(E')} v^{E'} with v = (a−b)x/(1+bx). This is an identity of rational functions between polynomials. So in characteristic p, Z_q = Z_{q mod p}.
- If q ≡ 0, then Z ≡ 0, since k ≥ 1.
- If q ≡ 1, then Z = Π(1+bx)(1+v) = Π(1 + ax).
- If a = b, the product is trivial.

**Hard side.** Let r := q in characteristic 0, or q mod p in characteristic p, and assume r ≥ 2 and a ≠ b. Then char ≠ 2 automatically, and r(r−1) ≠ 0 in F. Work with r colours.

- **Two pins.**
  - The pencil contains J − I, up to a scalar: take x = −1/a, or A itself if a = 0.
  - Join g₀ and g₁ by J − I. By S_r symmetry, Z = r(r−1) · Z[σ(g₀) = 1, σ(g₁) = 2].
- **Restriction and field in one step.**
  - Every free vertex v gets the edge v–g₀ with series x such that the edge function is ∝ J + zI. This uses x = z/((a−b) − bz), which is invertible since a ≠ b.
  - It also gets the edge v–g₁ ∝ J + ρ_v z I.
  - The product of the two is 1 + z[σ_v = 1] + ρ_v z[σ_v = 2].
  - The part of z-degree exactly n′ (the number of free vertices) is Π_v ([σ_v=1] + ρ_v[σ_v=2]). This restricts every free vertex to colours {1, 2} and puts an arbitrary unary ratio ρ_v on it, constant or 1 + z_v.
- **Reduction to Theorem 1.**
  - On colours {1, 2}, the pencil restricts to [[1+λa, 1+λb], [1+λb, 1+λa]], which is not a = b = c.
  - So Lemmas 2 and 3 (with ρ_v in place of the gadgets) and the assembly apply verbatim.
  - Use multigraded truncation (T2) in z (top degree n′) and in the z_v (degree ≤ N). ∎

## 6. Dependencies, checks and novelty

**Base.** The hard base is per3 (C-V4-a, internal) through C41's characteristic-free identity IP(G_N) = per3_N. There are two fallbacks:
- In characteristic ≠ 2, the permanent itself suffices: per_N is the folklore projection of per3.
- In characteristic 2, G3 Thm A's HC constraint network uses only NAND-type tables, Z₀₁-type tables (a generic 3-path B·μ·B·ν·B with ν chosen to kill entry (0,1)), and unaries. All of these are available here, so HC can replace per3.

**C++ sanity run (not part of the proof).** `[local reference omitted]` brute-forces the whole spin network, over F₁₀₀₀₀₀₃, F₇, F₁₃ and GF(256), for the three-vertex host (IP of a triangle) with random weights t. Totals: **0 failures**.
- **T1 end-to-end**, "model value = predicted constant × IP(G;t)":
  - generic pendant gadgets: 107/107 runs;
  - balanced triangle: 63/63;
  - W = 0 pendant-of-pendant: 47/47;
  - W = 0 with a + c = 2b triangle: 44/44;
  - char-2 pendant-of-pendant: 21/21;
  - pinned symmetric case: 38/38.
- **T2.** No determinant degeneracy occurred except at non-generic constants over F₇ and F₁₃ (3 cases), as expected.
- **T3.** Potts Z_q = Z_{q mod p}: 72/72.
- **T4.** Char-2 symmetric Z ≡ 0: 20/20. Z = 2·Z_pinned for w₀ = ±w₁: 120/120.

**Novelty and priority** (3 web queries):
- de Rugy-Altherre 1210.7641 proves a dichotomy only for unweighted 0/1 targets H (easy iff H has a loop or no edge), in characteristic 0, under c-reductions. It has no weights, no vertex weights and no characteristic p.
- The multivariate Tutte polynomial with edge-dependent (X_e, Y_e, x_e, y_e) weights is VNP-complete (cited in the survey arXiv 1910.08915). There q is not a fixed constant.
- The Boolean #P dichotomies (Goldberg–Jerrum–Paterson, Cai–Lu–Xia, Dyer–Goldberg–Jerrum) have much larger tractable sets: rank 1, bipartite, affine. The algebraic picture is qualitatively different. Variable edge selection destroys every Boolean tractable class except the trivial ones, apart from the char-2 vanishing (E3) and the char-p collapse Z_q = Z_{q mod p}.
- No algebraic (VNP) two-spin or Potts classification over arbitrary fields was found. **Likely new**, with gadget-level difficulty.

**Top-30 case.**
- It is a complete, explicit, every-field dichotomy for the two most-studied spin systems.
- It closes the C2/C17/C65 open boxes (non-zero field, q ≥ 3, characteristic 2, small fields).
- It settles A3's char-2 two-term signatures.
- Corollary 1 is a clean statement in its own right: the fixed-q multivariate Tutte polynomial is in VP iff q ∈ {0, 1}.
- Weaknesses:
  - the techniques are standard gadgetry plus division elimination;
  - hardness is a VP-transfer, not p-projection completeness;
  - non-integer q in characteristic 0 and general q×q spin matrices (q ≥ 3) remain open.
- **Estimated placement: about #18–25.**
