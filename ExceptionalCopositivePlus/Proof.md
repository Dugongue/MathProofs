# An exceptional copositive-plus matrix on the boundary of the copositive cone

**Date:** 2026-11-10

**Status:** Self-contained informal proof and exact rational certificates; not peer-reviewed or independently checked by the paper's authors.

**Published source:** I. M. Bomze and M. Dür, “A Square Departure From Symmetry in Matrix Cones,” *Vietnam Journal of Mathematics* **53** (2025), 757–771, §4, especially the paragraph following Theorem 4.8 and Corollary 4.14. https://doi.org/10.1007/s10013-024-00722-x

**Methodological inspiration:** Finite exact positivity witnesses, strict interior perturbation, a common padded witness, and preservation of a separating functional through limiting/extension operations; compare the finite Wilson measure → selected hierarchy → positive Gram-matrix pattern in https://github.com/yang-mills-group/OpenAI-YM-20261028. No Yang–Mills mathematical theorem is assumed here.

## 1. The actual published open question

The paper says explicitly: **“It is an open question whether there are exceptional copositive-plus matrices.”** It subsequently focuses on boundary examples and the possible failure of positivity on an enlarged simplex (the converse of its Theorem 4.3). The authors' definition of *exceptional* is a copositive matrix outside the cone `PSD_n + N_n`, where `N_n` consists of entrywise nonnegative symmetric matrices. A symmetric matrix `Q` is *copositive-plus* if

- `x^T Q x >= 0` for every coordinatewise nonnegative `x`, and
- whenever `x >= 0` and `x^T Q x = 0`, one has `Qx=0`.

Strictly copositive matrices satisfy the latter condition vacuously. To avoid that triviality we give a **boundary** example having an actual nonzero nonnegative zero vector. Moreover, our example fails `Γ_δ`-copositivity for *every* δ>0, which is the stronger type of example contemplated in the paper's Corollary 4.14.

## 2. Explicit answer

**Theorem.** The following symmetric `6×6` rational matrix is copositive-plus, belongs to the boundary of the copositive cone, is exceptional (not the sum of a positive-semidefinite and an entrywise nonnegative matrix), and is **not** `Γ_δ`-copositive for any `δ>0`:

```
Q = [ 0       0    0    0    0    0 ]
    [ 0     11/10 -1    1    1   -1 ]
    [ 0      -1  11/10 -1    1    1 ]
    [ 0       1   -1  11/10 -1    1 ]
    [ 0       1    1   -1  11/10 -1 ]
    [ 0      -1    1    1   -1  11/10 ]
```

### Step 1 — Start with a copositive exceptional 5×5 core

Let `A` be the adjacency matrix of the cycle `C5`, `J` the all-ones matrix, and `I` the identity matrix. Put

```
H = J - 2 A
R = H + (1/10) I.
```

Thus `H` is the classical Horn matrix and `Q = diag(0,R)`.

To show **copositivity** without importing Horn's theorem, let `y >= 0` and write `s = sum_i y_i`. Then

```
y^T H y = s^2 - 4 * sum_{i mod 5} y_i y_{i+1}.
```

On the simplex `s=1`, the edge-product sum is at most `1/4`. Here is a short proof: if the support contains two nonadjacent vertices `i,j`, keep `y_i+y_j` fixed and put all their mass at whichever of `i,j` has the larger neighbor sum. Since they are not adjacent, the edge-product sum is affine in this redistribution and does not decrease. Repeating eventually leaves support on a clique of `C5`, which has at most two vertices. On an edge with masses `a,b` summing to one, `ab <= 1/4`. The inequality follows; rescaling gives it for every `s`. Hence `H` is copositive.

It follows that

```
y^T R y = y^T H y + (1/10) ||y||^2
          >= (1/10) ||y||^2   for every y >= 0.
```

Thus `R` is **strictly copositive**.

### Step 2 — The padded matrix is copositive-plus and on the boundary

Write `x=(a,y)` with `a>=0`, `y in R^5_+`. Then

```
x^T Q x = y^T R y >= (1/10)||y||^2.
```

The quadratic form vanishes exactly when `y=0`, at which point `Qx=0`. This is precisely copositive-plus. Taking `x=e_1` gives `x^TQx=0`, proving `Q` is *not* strictly copositive and lies on the boundary of the copositive cone. On the probability simplex its zero set is exactly `{e_1}`.

### Step 3 — A strictly positive semidefinite separator proves exceptionality

Consider the rational `5×5` matrix

```
W = I + (3/5) A
  = [ 1    3/5   0    0    3/5 ]
    [ 3/5   1   3/5   0     0  ]
    [ 0    3/5   1   3/5    0  ]
    [ 0     0   3/5   1    3/5 ]
    [ 3/5   0    0   3/5    1  ].
```

Every entry of `W` is nonnegative. `W` is **positive definite**; an exact Sylvester-criterion certificate consists of its five leading principal minors:

```
1, 16/25, 7/25, 31/625, 11/3125.
```

For any PSD matrix `S`, `tr(SW)>=0`; for any symmetric entrywise nonnegative `N`, `tr(NW)>=0`. Therefore, if `R=S+N` with such `S,N`, necessarily `tr(RW)>=0`.

But the exact Frobenius pairing is

```
tr(R W) = tr((J - 2A + I/10)(I + 3A/5))
        = tr(J) + (3/5)tr(JA) - (6/5)tr(A^2) + (1/10)tr(I)
        = 5 + (3/5)*10 - (6/5)*10 + 1/2
        = -1/2 < 0.
```

Here `tr(A)=0`, `tr(JA)=10`, and `tr(A^2)=10`. Equivalently, the five diagonal positions contribute `11/2`, while the ten off-diagonal cycle-edge positions contribute `-6`. Thus `R` cannot belong to `PSD_5 + N_5`.

If `Q` belonged to `PSD_6 + N_6`, then its lower-right `5×5` principal submatrix `R` would also belong to `PSD_5 + N_5` (principal submatrices preserve both conditions), a contradiction. So `Q` is **exceptional**.

### Step 4 — Failure of every enlarged-simplex positivity test

The paper defines

```
U_δ = { x in R^6 : sum_i x_i = 1 and x_i >= -δ/6 for each i },
Γ_δ = R_+ U_δ.
```

For any `δ>0`, choose `0<t<δ/6` and let

```
x_t = (1, t, t, 0, -t, -t).
```

The coordinates of `x_t` sum to one and each is at least `-δ/6`. Thus `x_t in U_δ`. Writing `v=(1,1,0,-1,-1)` for its last five coordinates divided by `t`, we calculate exactly

```
sum_i v_i = 0,
||v||^2 = 4,
sum_{cycle edges} v_i v_{i+1} = 1,
v^T H v = -4,
v^T R v = -4 + 4/10 = -18/5.
```

Consequently

```
x_t^T Q x_t = -(18/5) t^2 < 0.
```

Since this works for *every* `δ>0`, `Q` is **not** `Γ_δ`-copositive for any δ.

This also shows that copositive-plus does not generally imply `Γ_δ`-copositive, even in the symmetric setting.

**QED.**

## 3. General construction (not just one matrix)

Let `R` be *any* strictly copositive real symmetric `m×m` matrix outside `PSD_m + N_m`. Then `Q = diag(0,R)` is an `(m+1)×(m+1)` **boundary exceptional copositive-plus matrix**. If `R` is not PSD, then `Q` is not `Γ_δ`-copositive for any δ, since `R` has a negative quadratic direction and that direction can be approached from the zero coordinate of `Q` along the affine simplex.

For our specific Horn core the rational one-parameter family

```
Q_ε = diag(0, H + ε I),     0 < ε < 1/5,
```

works: strict copositivity holds for every ε>0; the same matrix `W` gives `tr((H+εI)W)=5ε-1<0`. So there is an *entire open interval* of boundary exceptional copositive-plus examples, not merely an isolated construction.

The dimension-6 example is important: for orders at most four `COP_n = PSD_n + N_n`, so the zero-padding argument requires an exceptional core in dimension at least five.

**A version with every diagonal entry strictly positive.** If one objects to a zero row and column, define `S = [[1,-1],[-1,1]]` and the `7×7` matrix `Q^+ = diag(S,R)`. For nonnegative `x=(u_1,u_2,y)`,

```
x^T Q^+ x = (u_1-u_2)^2 + y^T R y >= (u_1-u_2)^2 + ||y||^2/10.
```

Its nonnegative zeros are exactly `(a,a,0,0,0,0,0)`, all belonging to its kernel; thus it is boundary copositive-plus. It is exceptional by its `R` principal submatrix and has all seven diagonal entries strictly positive. For `0<t<δ/7`, `x_t=(1/2,1/2,t,t,0,-t,-t)` belongs to `U_δ` and satisfies `x_t^T Q^+ x_t=-18t^2/5 < 0`. Thus it also fails every enlarged-simplex test. The original `6×6` example remains the smallest example given here.

## 4. A separate issue: Theorem 4.8 appears false as printed

The journal paper's Theorem 4.8 states that a copositive-plus matrix in its symmetrized `PSD+N` cone is `Γ_δ`-copositive for all sufficiently small δ. In the **symmetric** case the following `3×3` matrix already refutes this statement:

```
B = [0 0 0]
    [0 1 2]
    [0 2 1].
```

Every entry of `B` is nonnegative, so `B in N_3`. For `x=(a,b,c)>=0`,

```
x^T B x = b^2 + 4bc + c^2 >=0,
```

with equality only if `b=c=0`; then `Bx=0`. Hence `B` is copositive-plus.

However, for every `δ>0` and `0<t<δ/3`, the vector

```
y_t = (1,t,-t) in U_δ,
```

and

```
y_t^T B y_t = -2t^2 < 0.
```

Thus **no** δ works. This conflicts not just with Theorem 4.8 as printed but also with its Corollary 4.14, whose first conclusion requires dimension at least five for such a counterexample. The issue is that *strict copositivity of a nonnegative principal block on its own nonnegative orthant does not control its quadratic form on sign-changing directions arbitrarily close to a zero face*.

This auxiliary claim is a direct check against the article's stated definitions. It does not require that the authors' intended theorem was the same as the printed wording; clarification or a corrigendum may exist that the search did not find.

## 5. Why this counts as a transfer of proof techniques

The mathematical result does **not** import or depend on the large Yang–Mills construction. The transferable *architecture*, however, is genuine:

- **Finite positive seed:** `H` has a genuine copositivity certificate, just as Wilson lattice measures provide finite positive objects.
- **Strict perturbation / stability margin:** `R=H+εI` removes unwanted zeros while retaining exceptionality by a quantitatively negative dual pairing.
- **Padding preserving the exact witness:** `diag(0,R)` exposes a controlled zero face without destroying the positive core or the separator. This resembles the repository's insistence on one common hierarchy carrying positivity and all observable tests at once.
- **Adversarial off-cone test:** The sign-changing vector near the zero face supplies an explicit hostile witness to an overly strong positivity-extension statement.

These are proof-design techniques, not a claim of logical dependence on Yang–Mills or of an independently checked literature-first discovery.

## 6. Verdict and checks still needed for publication

1. **Published open question, as stated:** answered **YES** by the exact `6×6` example, even requiring a genuine boundary zero and failure of every `Γ_δ` test.
2. **Published theorem/corollary, as printed:** the explicit `3×3` `B` is a counterexample to the claimed converse and the dimension lower bound.
3. **Arithmetic:** all certificates are rational and were checked by exact symbolic arithmetic (the Gram separator's leading minors, `tr(RW)=-1/2`, and `v^TRv=-18/5`).
4. **Novelty / publication:** the journal source itself explicitly poses the question; a search did not locate a later correction or matching published answer. That is *not* a comprehensive priority search. External expert scrutiny and author feedback would be prudent before claiming priority or publishing.

### References

- I. M. Bomze and M. Dür, “A Square Departure From Symmetry in Matrix Cones,” *Vietnam J. Math.* **53** (2025), 757–771, DOI: https://doi.org/10.1007/s10013-024-00722-x
- The classical Horn matrix and copositivity: see the cited paper's §4 and its bibliography; our proof of copositivity is self-contained.
- Yang–Mills repository used only for method inspiration: https://github.com/yang-mills-group/OpenAI-YM-20261028
