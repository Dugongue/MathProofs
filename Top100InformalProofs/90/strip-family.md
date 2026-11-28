# The EHPS strip construction and its restricted optimum

The optimality conclusion is for the strip family defined below.

## 2. Lower bound: the EHPS block method, made computable

### 2.1 What drives the constant (proved, by re-deriving EHPS Prop 2.1, 3.1 and Thm 1.1)
Call a set T ⊂ [0,1)^d a *block* if there is a bounded measurable f with

  (B)  f(x) + f(z) >= 2 f(y) + |x - z|^2   for all x, y, z ∈ T with x + z ≡ 2y (mod 1).

Then r_3(N) >= N 2^{-(2 sqrt(2 ℓ) + o(1)) sqrt(log_2 N)}, where ℓ = log_2(1/δ) and δ = μ(T)^{1/d}.
- Behrend has δ = 1/2.
- EHPS has δ = sqrt(7/24) = 0.540.

The factor 2 in "2ℓ" is the exponent s = 2 in "#slices ~ ε^{-s}". **No-go (sketch, 90%): s = 2 cannot be lowered.** A positive-measure T contains honest AP chains of about 1/ε steps at spacing ε. Along such a chain the increments of f must grow by at least η per step, so sup f / η ≳ ε^{-2}. So all of the gain has to come from δ.

**Ceiling for the method (proved, given Ellenberg–Gijswijt / Blasiak et al.):** a block gives r_3(Z_p^n) ≳ (δp)^n, so δ <= 0.8414. The best constant this method could ever reach is therefore C >= 2 sqrt(2 log_2(1/0.8414)) = 1.41.

### 2.2 Lemma B (proved): circular distance suffices
In (B), |x - z| may be replaced by the torus distance ||x - z||. Both of EHPS's deductions (through Z_{m_1} × ... × Z_{m_n}, and through Green–Wolf a + xb mod 1) use only one fact: distinct points have some coordinate that is far apart on the circle. So the block property is invariant under translation and under x ↦ -x. (It does not help the g-scheme below, because the failing cases there have a negative defect of order 1.)

### 2.3 Reformulation (proved, one line)
Put f = 2|x|^2 + h. Then (B) is equivalent to

  h(x) + h(z) - 2h(y) >= -4 k·y - |k|^2,   where k := x + z - 2y ∈ Z^d.

The identity used is 2|x|^2 + 2|z|^2 - 4|y|^2 - |x-z|^2 = |x+z|^2 - 4|y|^2 = 4k·y + |k|^2.

Consequences:
- On honest APs (k = 0), h must be midpoint-convex.
- For each pair x, y = x + k/2 with both points in T, h is rigid: h(x) - h(y) = -2k·y - |k|^2/2. Equivalently, f(x) = f(y).

### 2.4 Lemma A (proved): the EHPS scheme in general
Take d = 2, u = x1 + x2, g(t) = (t mod 1/2)^2 and f = (24/ε^2) u^2 + 6 g(x1). Then f satisfies (B) on any measurable T ⊂ [0,1)^2 with these two properties:
- **(L1)** No x, y, z ∈ T with 2y - x - z ∈ {e1, e2, e1+e2}. Equivalently, no triple has u-defect w = u(x+z-2y) < 0.
- **(F)** Take any x, y, z ∈ T with x + z ≡ 2y, w = 0 and |u(x) - u(z)| < ε, where x1 < 1/2 <= z1. Then x1 >= 1/4 and x1 + z1 >= 1.

The proof is EHPS §4 verbatim. Lemma 4.4 is replaced by (L1), and Lemma 4.6 together with Fact 4.3(ii) is replaced by (F). EHPS used only those facts about their particular T.

Necessity of (F) inside the scheme (proved): if x1 + z1 < 1, the g-defect equals (x1-z1)^2/2 - (z1 - 1/4) < 0 whenever z1 > 1 - 1/sqrt 2.

### 2.5 Binary-digit decomposition (proved)
Write each coordinate as x = (β + q)/2, with q ∈ {0,1}^2 the first binary digit and β ∈ [0,1)^2 the remainder. Let T_q = {β : (β + q)/2 ∈ T}. Then:
- T ↔ (T_00, T_10, T_01, T_11), and μ(T) = Σ|T_q| / 4.
- A triple x + z ≡ 2y corresponds to the base triple β_x + β_z - 2β_y = k'. Here k'_c = 0 if q_{x,c} = q_{z,c}, and k'_c = ±1 otherwise; so it is again a torus AP relation.
- With κ = 2y - x - z, the digits satisfy κ = q_y - (q_x + q_z + k')/2.
- Condition (F) for a pair that is mixed in coordinate 1 is equivalent to k'_1 = +1 together with β1 >= 1/2 for the lo point.

**Same-base rule (proved):** two points of T with the same β must have incomparable digits. So T_00 and T_11 are disjoint from everything else, and only the pair {10, 01} can share a base point. Hence

  μ(T) = (|T_00 ∪ T_10 ∪ T_01 ∪ T_11| + |T_10 ∩ T_01|) / 4 <= 1/2.

Write A = T_10, B = T_01, C = T_11. The full rule table is in LOG-E2. The rules that matter:
- A ∩ C = B ∩ C = ∅.
- mid(A,A) ∩ C = ∅ and mid(B,B) ∩ C = ∅.
- (A + B + (1,1))/2 ∩ (A ∪ B ∪ C) = ∅.
- (A + B ∓ (1,-1))/2 ∩ C = ∅.
- (A + C + (0,1))/2 ∩ C = ∅ and (B + C + (1,0))/2 ∩ C = ∅.
- Near-tight rules (with s := β1 + β2, so that u = (s + |q|)/2):
  - an A–B pair on the same s-line must not have (β_A + β_B + (1,-1))/2 ∈ A ∪ B;
  - a B–C pair with s_B ≈ s_C + 1 must not have (β_B + β_C + (1,0))/2 ∈ A ∪ B;
  - B-points that lie in near-tight triples need β1 >= 1/2.
- C × C triples are always allowed.

EHPS in this language:
- A = {1/3 < s <= 11/6}, which covers 67/72 of the base square;
- B = {4/3 < s <= 11/6, β1 >= 2 - s}, area 13/72;
- C = {s <= 1/3};
- T_00 = ∅.

This gives 4μ = 71/72 + 13/72 = 7/6.

### 2.6 Theorem S (proved; Monte-Carlo cross-checked): 7/24 is optimal in the natural strip family
Fix c ∈ [0, 1/2] and set e = c + 3/2. Define
- C = {s <= c},
- A = {c < s <= e},
- B = {c+1 < s <= e, β1 >= max(2-s, s-1)}, with ε-margins.

These satisfy (L1) and (F). The resulting area is μ(c) = (1 + c - (3/2)c^2)/4, maximised exactly at c = 1/3, where μ = 7/24 (EHPS).

The constraints force the shape:
- **e <= c + 3/2:** otherwise (A+B+(1,1))/2 lands in A by the s-count.
- **B lies above s = c+1:** the near-tight B–C rule.
- **β1 >= 2 - s on B:** the near-tight A–B rule.

Within full-line strips there is no other option: replacing C by [0,c] ∖ R forces R to be an upper interval, by the mid(A,A) ∩ C rule. Neither the T_00 slot nor the uncovered corner s > 11/6 can be used, because (D+A+(1,0))/2 lands in A, and C-points there violate the (A+C+(0,1))/2 rule.

**Flat direction (proved):** at c = 1/3, removing C on line σ for β1 < γ and adding B on line σ+1 for β1 >= 1 - γ leaves the area exactly unchanged. Any improvement on 7/24 inside the scheme must therefore come from genuinely two-dimensional (non-strip) shapes.

Cross-check: `mc.cpp` samples triples of T and tests (B) directly for the actual f.
- c = 1/3, 0.2 and 0.45: 2.2M triples each, 0 violations; areas match μ(c) up to the margins.
- Negative controls fail as expected: e = 1.95 gives 597 violations, and a B-cut lowered by 0.1 gives 98.
