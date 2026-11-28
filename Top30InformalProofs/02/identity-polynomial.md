# Noncommutative identity polynomial bounds over every field

Conditional on the stated planar and flat bounds. Field and circuit-model restrictions are given in the proof.

## Inputs used, by owner

| tag | input | status |
|---|---|---|
| [OAI] | `HasSpectralFlat K 2` for every field K (Lean `OAI.Hierarchy.HasSpectralFlat.plane`); oaG Cor 6.2 (two crossing cuts, every field, Zariski closure) | treated as proved (directive) |
| [OAI-flat] | for every price P on ℝ² over any field, price(diag_S) = meanWidth(S). Lean: `flatDiagonalLaw_isometry` + `jointlyConvexDiagonal_of_raw` + `SiteTensor.rawDiagonalJointConvexity K` (SpectralFlatLaw.lean:115, PlacedDiagonal.lean:79, BinaryJointConvexity.lean:36) | treated as proved. Used only for constants; every exponent also holds with the axiom-level star bound c ≤ 4 |
| [Liu] | two-hub layouts, the closure-to-exact tensor-power step (2611.00994 §2) | audited PASS |
| [HWY] | Prop 3.2 (C(f) ≥ Ω(d⁻³ w(f))), Lemma 3.5 (degree-4 central pieces are type (a) or type (b)), Remark 4.2. All are characteristic-free (hwy.txt l.586–710, 834–851) | published, JAMS 2011 |
| [ours] | glue (audit-L2-glue, PASS); the width-to-two-cut step; char 2; exact-distance and mean-width constants; atomic copy polynomials; Boolean reading | this file |

## S1. Theorem (identity polynomial, every field)

Let K be **any** field, of any characteristic, 2 included. Let k ≥ 2, r = ⌊log₂ k⌋ and c = 2√2. With the axiom-only constant c = 4 the bound changes only in the √r term.

(i) For ID_k = Σ_{i,j≤k} x_i y_j x_i y_j and for g_k = Σ_{i,j≤k} x_i x_j x_i x_j, every noncommutative circuit over K has size

  C ≥ Ω(2^{h(r)}),  where h(r) = max_{0<t≤1} [4r(1 − √(1 − √2·t + t²)) − c]/(2t) ≥ √2·r − √(2cr).

So C ≥ k^{√2}·2^{−O(√log k)}. The same holds for border size, i.e. Zariski closure over K̄.

(ii) Rectangular version: ID_{k,m} = Σ_{i≤k, j≤m} x_i y_j x_i y_j needs size 2^{√(a²+b²) − O(√min(a,b))}, where a = ⌊log₂k⌋ and b = ⌊log₂m⌋. For m = k^α this is k^{√(1+α²)−o(1)}.

(iii) Atomic copy polynomials: CP_{d,k} = Σ_{w∈[k]^d} w·w has degree 2d. It needs size k^{λ_d − o(1)} as k → ∞ with d fixed. Here λ_d is the descent-game value on the regular 2d-gon with unit sides:

| d | 2 | 3 | 4 | 5 | 6 | 8 | 16 |
|---|---|---|---|---|---|---|---|
| λ_d | √2 | √3 | 1+√2 | 3.078 | 3.346 | 4.736 | 8.998 |

The trivial upper bound is k^d. Liu's bit-level route via D_{dr} gives only k^{d/2}; C1's circle gives k^{0.551d}.

**Why it is new.**
- HWY's Thm 1.6 bounds C(ID_k) by B_F(SOS_k). In characteristic 2 that is useless: (Σx²)(Σy²) = (Σx_iy_j)², so B = S = 1. The same holds for C3's Theorem C, which routes through S_{F̄} and polarization (char ≠ 2), and for H24.
- In char 2, no superlinear bound for any explicit degree-4 nc polynomial was known. H24's subquadratic upper bound O(k^{1.96}) is also char ≠ 2 only (H24 l.27–28, Thm 3).
- So in char 2, (i) is the only nontrivial bound on either side: k^{√2−o(1)} ≤ C(ID_k) ≤ O(k²).

### Proof of (i)

1. **Width ⇒ two-cut decomposition [HWY, char-free].**
   - A size-s nc circuit for a degree-4 polynomial f has a homogeneous version of size O(s) (Lemma 3.3).
   - Prop 3.2 then writes f = Σ_{t≤n} f_t with n = O(s) central pieces. By Lemma 3.5 each piece is
     - (a) g_t[pos 1,2]·h_t[pos 3,4], or
     - (b) Σ_i h_{t,i}[pos 1]·g_t[pos 2,3]·h'_{t,i}[pos 4].
   - Nothing in Prop 3.2 or Lemma 3.5 uses the characteristic.
   - On coefficient tensors in (K^{2k})^{⊗4}:
     - a type (a) piece has flattening rank 1 across {1,2}|{3,4};
     - a type (b) piece has flattening rank 1 across {2,3}|{4,1}.
2. **Restrict.**
   - Let q = 2^r ≤ k, and apply the position-local projections onto x_1..x_q at positions 1 and 3 and onto y_1..y_q at positions 2 and 4. For g_k, use x_1..x_q everywhere.
   - In both cases the image of the coefficient tensor is exactly C_r = Σ_{i,j≤q} e_i⊗e_j⊗e_i⊗e_j = [a=c][b=d], with r bits per leg.
   - Local maps do not raise flattening ranks. Hence C_r = T₁ + T₂ with rank_{ab|cd}T₁ ≤ n and rank_{bc|da}T₂ ≤ n.
   - (This also answers STEER 21:25. HWY Remark 4.2 gives w(ID_k) = w(g_k) exactly, characteristic-free. Here the coefficient tensor of g_k already **is** C_r, so no ID ↔ ID′ constant is needed at all.)
3. **Two-cut glue [OAI + Liu layouts + ours].**
   - Place a, b, c, d at e₁, e₂, −e₁, −e₂. Then price(C_r) = 4r.
   - T₁ is a restriction of the network with hubs at ±tz, z = (e₁+e₂)/√2, and a ⌈log₂n⌉-bit cable. T₂ uses the same network with z′ = (e₂−e₁)/√2.
   - Exact cost: each bit is at distance √(1 − √2t + t²) from its hub. So cost ≤ 4r√(1−√2t+t²) + 2t⌈log₂n⌉.
   - Price ≤ cost and the sum rule with A = 2 give 4r ≤ max cost + c·log₂2, where c = price(diag_{±e_i}) = W(square) = 2√2 [OAI-flat], or c ≤ 4 (star bound, axioms only).
   - Hence ⌈log₂n⌉ ≥ h(r). The bound h(r) ≥ √2r − √(2cr) follows from √(1−√2t+t²) ≤ 1 − t/√2 + t²/2 with t = √(c/(2r)).
4. **Conclude.** s ≥ Ω(n) ≥ Ω(2^{h(r)−1}).
5. **Border.**
   - For fixed s, the degree-4 output tensors of all circuits of that shape lie in S_n = {T₁+T₂ : rank bounds as above}, which is a set of sums of restrictions of two fixed networks.
   - Liu's closure-to-exact step applies verbatim, and oaG Cor 6.2 states the closure version directly: C_r^{⊗q} is a sum of poly(q)·2^q networks of cost ≤ qw. This gives 4r ≤ w + c, with a non-strict limit. ∎

**(ii).** Steps 1, 2 and 4 are unchanged, with legs of a and b bits. Step 3 is C3's Theorem A layout: weighted hubs on z = (a e₁ + b e₂)/|v|, giving h ≥ √(a²+b²) − tμ − c/(2t). That is valid over every field here, because no polarization is used. ∎

**(iii).**
- Restrict each of the 2d letter positions to q = 2^r letters. The coefficient tensor becomes Π_{l≤d} EPR_q(l, l+d).
- Put position l at the unit vector of angle π(l−1)/d, so partners are antipodal and the sites are distinct. Price = star cost = 2dr.
- The gates' intervals are letter intervals, so Liu's descent runs on the regular 2d-gon with side r. The game value is λ_d·r: it is the min over binary trees of the max node chord, which equals the Chooser game (val(I) = max(chord I, min_k max(val, val))).
- Two-hub layouts and the glue use c = W(2d points on the unit circle) ≤ π [OAI-flat] and A ≤ (2d+1)². They give log C ≥ λ_d r − O(√(d r log d)).
- λ_d was computed exactly by the DP in lstar.cpp (mode 1, n = d). λ_2 = √2 is the square's diagonal, λ_3 = √3, λ_4 = 1+√2 is the octagon's 3-step chord, and λ_5 = 2ρ sin(2π/5) with ρ = 1/(2 sin(π/10)). ∎

### Self-audit (K4)

- **Is Prop 3.2 really char-free?** Yes. Its proof is an induction on gates that splits sums and products by degree (l.595–662). The only field-dependent statement in HWY §3–4 is Prop 4.1(ii) ("char ≠ 2 … w ≤ 4B"), which we do not use.
- **Type (b) rank.** Σ_i h_{t,i}[1] g_t[2,3] h′_{t,i}[4] = (coef g_t on legs 2,3) ⊗ (Σ_i h_{t,i} ⊗ h′_{t,i} on legs 1,4). That has rank 1 across 23|41. ✓
- **Pieces of type (a) at positions {3,4}.** Under the d₀ = 2, d₁ = 2 case of Claim 3.4 they are still a product of a degree-2 polynomial on {1,2} and one on {3,4}, hence still rank 1 across ab|cd. ✓
- **Consistency with known upper bounds.** In char ≠ 2, H24 gives C(ID_k) ≤ k^{1.96}, which is above k^{√2}. oaG Cor 6.2 claims the two-cut exponent √2 is sharp, so the method cannot give more. Liu's converse kill test also passes: no known two-cut decomposition has exponent < √2.
- **Is it already in Liu?** No. Liu §2 states only the complex SOS corollary, with no ID_k, no width, and no char 2.
- **Is it already in OAI?** No. Their preprints contain no noncommutative or circuit content (audit-L2-glue §7; C1 K0 grep).

## S2. Boolean reading over F₂ (minor; the substance is oaG Cor 6.2)

Let f(a,b,c,d) = [a=c ∧ b=d] on four r-bit strings. Suppose f = G ⊕ H over F₂, with rank_{F₂} of G across (a,b)|(c,d) at most R and rank of H across (b,c)|(d,a) at most R. Then log₂R ≥ h(r) ≥ √2r − O(√r). This is Cor 6.2 / the glue over F₂.

**Corollary.**
- Suppose G has a deterministic protocol, or any disjoint 1-rectangle cover, of cost C₁ for the partition {a,b} vs {c,d}, and H has one of cost C₂ for {b,c} vs {d,a}. Then max(C₁, C₂) ≥ √2r − O(√r).
- The trivial protocol gives 2r + 1.
- An elementary rank argument gives nothing here. A {b,c}|{d,a}-rectangle X(b,c)×Y(d,a) can have full rank q² across ab|cd, so subadditivity is vacuous.

This is the honest answer to "an F₂ sum-of-squares bound". The SOS identity itself is degenerate in char 2, and realification F₄ → F₂ keeps it degenerate (C4-01 killed). The two-cut statement is the char-free content, and S1 is its circuit consequence.

## S3. Quantitative: what c and ω do to the exponents (answers the lane question)

**c ∈ [2, 4] (the audit's c).**
- In every Liu-type bound, c enters only through the second-order term √(2c·n·log A). The leading constant (n/2 for Liu, √3/π for C1, √2 for SOS and ID_k) is pure chord geometry.
- c does change the *effectivity threshold* of the two-cut bound, i.e. the first r = log₂q where it beats the trivial R ≥ q. From thresh.cpp:

| c | quadratic distance bound (Liu) | exact distance |
|---|---|---|
| 4 (star, axioms only) | r ≥ 47 (= L4) | r ≥ 30 |
| 2√2 (true value, OAI flat law) | r ≥ 33 | **r ≥ 21** |
| 2 (lower limit) | r ≥ 24 | r ≥ 15 |

  So S_ℂ(q) > q, and C(ID_k) beyond linear, are certified from q = 2^21 on, not 2^47.
- For many-terminal placements, the flat law gives c = W(Pt) ≤ π however many sites there are. The star bound grows with the number of sites (2n), and C1 needed a separate path bound (c < 2π). With W ≤ π the circle theorem's error term is O(√(n log n)) directly.

**ω = 9/4.** No effect (killed, K1).
- Lemma 2.1 and Lemma 3.1 involve no three-party tensor.
- Placing ⟨n,n,n⟩ on a triangle gives wire price 3√3·log n against a star cost of 6·log n. The leading term does not cancel, so no two-hub argument applies.

**The n/2 exponent.** It does improve, by geometry rather than by c or ω: C1's √3/π (my C4-07 is an independent rediscovery). The descent method is capped at 2/3 in every dimension. My hill-climbs (D = 2, 3, 4; n = 24, 32, 48) agree with C1 that the circle is optimal up to discretisation.
