# Rectangular Hurwitz lower bounds

The lower bounds in this report depend on the indicated unrefereed inputs. The parity-representation consequence is indexed separately under rank 17.

## Theorem A (rectangular Hurwitz problem, every field of char ≠ 2)

Let char F ≠ 2. Set a = ⌊log₂n⌋, b = ⌊log₂m⌋, μ = ab(a+b)/(a²+b²). Note μ ≤ 2·min(a,b), and μ = a when a = b. Then for every t ∈ (0, 1/2]:

  ⌈log₂ σ_F(n,m)⌉ ≥ √(a²+b²) − tμ − 2/t.

In particular, if μ ≥ 8:
  log₂σ_F(n,m) ≥ √(a²+b²) − 2√(2μ) − 1 ≥ √(a²+b²) − 4√min(a,b) − 1.

So σ_F(n, n^α) ≥ n^{√(1+α²) − o(1)}. The balanced case a = b = r gives Liu's √2·r − 2√(2r) exactly.

**Proof.**
1. **Restrict.** Zero the variables beyond 2^a and 2^b. This leaves a formula of type [2^a, 2^b, s].
2. **Polarize** (char ≠ 2).
   - Polarizing in x gives Σ_k f_k(x,y)f_k(x′,y) = ⟨x,x′⟩⟨y,y⟩.
   - Polarizing that in y gives ½Σ_k[f_k(x,y)f_k(x′,y′) + f_k(x,y′)f_k(x′,y)] = ⟨x,x′⟩⟨y,y′⟩.
   - Call the two halves T₁ and T₂. The right-hand side is C = [X₊=X₋][Y₊=Y₋], with a bits on X and b bits on Y.
   - T₁ has flattening rank ≤ s across {X₊,Y₊}|{X₋,Y₋}. T₂ has flattening rank ≤ s across {X₊,Y₋}|{X₋,Y₊}.
3. **Layouts.** Place X± at ±e₁ and Y± at ±e₂. Let v = a·e₁ + b·e₂ and z = v/|v|.
   - T₁: one node at tz holding the table f(x,y), one at −tz holding f(x′,y′), and an h = ⌈log₂s⌉-bit cable between them.
   - T₂: the same with z′ = (a·e₁ − b·e₂)/|v|.
4. **Distance bound.** For a unit vector u with α = ⟨u,z⟩ and t ≤ 1/2:
   |u − tz| = √((1−tα)² + t²(1−α²)) ≤ 1 − tα + t²(1−α²).
   - Weighting by a and b gives Σ a(1−tα₁) = a + b − t|v| and penalty t²·(ab² + ba²)/|v|² = t²μ.
   - So each layout costs ≤ 2(a+b) − 2t|v| + 2t²μ + 2th.
5. **Price of C.** By multiplicativity and the `wire` axiom, price(C) = 2a + 2b. Two wires of length 2.
6. **Apply the glue** with A = 2 (so c·log₂2 ≤ 4):
   2(a+b) ≤ 2(a+b) − 2t|v| + 2t²μ + 2th + 4, hence h ≥ |v| − tμ − 2/t.
7. **Optimize.** Take t = √(2/μ). ∎

The glue is stated in the audit for equal widths r. Its proof, steps (2)–(3), never uses equal widths: the sum rule and price(network) ≤ cost are width-agnostic. oaG Cor 6.2 is literally this unequal-width statement, asymptotically and over every field.

**C++ check** ([local reference omitted]). I optimized the exact-distance layouts over t. They match the closed form and are slightly better: at L₂ = 65536 the exponent ratio is 1.0024, 1.0265, 1.1120, 1.2428, 1.4064 for α = 0.1, 0.25, 0.5, 0.75, 1, against √(1+α²) = 1.0050, 1.0308, 1.1180, 1.2500, 1.4142. The bound beats the trivial max(n,m) once log₂min ≳ 2.5·(log₂max)^{2/3}.

### Corollaries of A
- **A1. Real and integer formulas.** A formula over ℝ or ℤ is a formula over every field containing it. So S_ℤ(k) ≥ S_ℝ(k) ≥ k^{√2−o(1)}.
  - This beats HWY Thm 1.10 (Ω(k^{6/5}), integer coefficients only).
  - It beats the best real lower bound, (2−o(1))k (HWY Thm 1.2, James / Lam–Yiu).
  - Over ℝ the best upper bound is still O(k²/log k). H24's construction needs √−1 or char p (H24 §7, Problem 2). So over ℝ the exponent now lies in [√2, 2].
- **A2. Signed intercalate matrices** (combinatorial; HWY Prop 7.1). Every k×k signed intercalate matrix has at least k^{√2−o(1)} colours. The r×s version needs 2^{√(a²+b²)−O(√min)} colours. The statement involves no algebra. (Unsigned intercalate matrices have k colours via i⊕j, so the signs are essential.)
- **A3. Positive characteristic.** σ_{F_p}(k,k) ≥ k^{√2−o(1)} for every odd p. H24 Thm 1 gives O(k^{1.62}) there. Previously nothing superlinear was known in char p.
- **A4. Linear spaces of similarities.** Let V be a real space of n×s matrices X, each with XᵀX = q(X)·I where q is positive definite. Diagonalizing q gives an [dim V, s, n] formula. So dim V ≤ 2^{√(log²n − log²s) + O((log n)^{3/4})}.
  - Example: for n = s^{1.2}, dim V ≤ s^{0.663+o(1)}.
  - The topological bound (Hopf–Stiefel) is only dim V ≲ n.
- **A5. Quadratic maps between spheres.**
  - Let F: ℝ^M → ℝ^N be quadratic with |F(x)| = |x|², and let e ∈ S^{N−1}. Let p and q be the dimensions of the +1 and −1 eigenspaces of ⟨F,e⟩.
  - Then F(u+w) = (|u|²−|w|²)e + 2β(u,w) with β ⊥ e and |β(u,w)| = |u||w|. This is a [p, q, N−1] formula. (Proof: F(u) = |u|²e because ⟨F(u),e⟩ = |u|² = |F(u)|. Also ⟨β(u,w),e⟩ = uᵀQw = 0.)
  - Hence N − 1 ≥ 2^{√(⌊log p⌋²+⌊log q⌋²) − O(√log)}. For example, a quadratic map S^{2q−1} → S^N of Hopf-construction type needs N ≥ q^{√2−o(1)}.
- **A6. Normed versus nonsingular: the topological approach is polynomially lossy.**
  - Nonsingular bilinear maps K^r × K^s → K^{r+s−1} exist over every field (polynomial multiplication).
  - Axial maps, Hopf–Stiefel, K-theory and immersion obstructions see only nonsingularity, so they can never give more than about r+s.
  - Hence S(k)/(k∘k) ≥ k^{√2−1−o(1)}: normed composition is polynomially harder than its topological shadow.
