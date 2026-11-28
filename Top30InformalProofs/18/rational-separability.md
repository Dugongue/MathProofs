# Hilbert’s tenth problem over the rationals and rational separability

The result concerns computable reductions. The stronger complexity and local versions are separate problems.

## 2. Definitions

All vectors and matrices are real. A, B are Q-vector spaces with standard bases; Sym(·) means symmetric matrices. A *rational product vector* is a⊗b with a ∈ Q^{dA}, b ∈ Q^{dB}. **Q-SEP** asks whether ρ ∈ cone_Q{ww^T : w rational product}. Weights can be dropped, because p·ww^T = Σ_k (q_k w)(q_k w)^T with p = Σ q_k² (Lagrange).

Two elementary facts are used throughout.

(R) **Range lemma.** If ρ = Σ c_j w_j w_j^T with c_j > 0, then every w_j ∈ range(ρ). (Standard: if x ⊥ range ρ, then 0 = x^Tρx = Σ c_j (x·w_j)².)

(M) **Marker lemma.** Fix z. If ρ = Σ_j λ_j w_j w_j^T (any real λ_j) and z^T ρ z ≠ 0, then some w_j has ⟨z, w_j⟩ ≠ 0.

## 3. Theorem A: compact HTP over Q is HTP(Q)

**CHTP.** The input is a polynomial system g(y) = 0 over Q together with a rational R such that every real solution satisfies |y_i| ≤ R. The question is whether the system has a rational solution.

**Theorem A.** HTP(Q) ≤_p CHTP ≤ HTP(Q). The same construction gives the analogous statement over any field F ⊆ R ⊗ … in which √2 ∉ F; it is used over Q(i) in Remark 6.3.

*Proof.* The direction CHTP ≤ HTP is trivial. For the other direction, start from f(x₁..x_k) = 0 of degree D, and let F(u,v) = v^D f(u/v) be its homogenisation. The system Σ_c in variables u ∈ Q^k, v, s ∈ Q⁵, z, t, σ ∈ Q⁵, τ ∈ Q⁵ is:

1. v² + Σ u_i² + Σ s_l² = 1
2. F(u, v) = 0
3. z² − 2 = v·t
4. 4 − z² = Σ σ_l²
5. 1 − t² = Σ τ_l²

Combine these into one equation by summing squares.

*Compact.* (1) gives |u_i|, |v|, |s_l| ≤ 1. (4) gives |z| ≤ 2 and |σ_l| ≤ 2. (5) gives |t| ≤ 1 and |τ_l| ≤ 1. So R = 2.

*Sound.* At a rational solution, v ≠ 0, because v = 0 forces z² = 2. Then x = u/v is rational and f(x) = v^{−D}F(u,v) = 0.

*Complete.* Let f(x) = 0 with x rational. Choose a rational v ≠ 0 with v²(1+|x|²) ≤ 1 and set u = vx. Then 1 − v²(1+|x|²) ∈ Q_{≥0} is a sum of four rational squares (Lagrange; five slots give slack). By density, choose a rational z with |z| ≤ 2 and |z² − 2| ≤ |v|. Put t = (z²−2)/v ∈ [−1, 1]. Then 4 − z² ≥ 0 and 1 − t² ≥ 0 are rational and are sums of squares. ∎

The point is that the non-closed condition v ≠ 0 is excised by an irrational limit point (z = √2 is the only real way to reach v = 0). Compact witness sets cost nothing over Q. The same trick drives Theorem B: the "√2-atoms" are the real-only witnesses.

*Novelty:* elementary, and probably folklore among HTP(Q) specialists, but I found no statement of it. It refutes the natural worry, raised implicitly in quantum.md G1, that compactness or properness is what separates PROJ-HTP from HTP. Compactness does not separate them. Properness at infinity of the *projective closure* is a different matter; G1 is still open.

## 4. Theorem B: the reduction

### 4.1 Input normal form

By Theorem A and the standard reduction of any Diophantine system to quadratic ones (introduce y_{ij} = y_i y_j; new variables are products of bounded ones, so they stay bounded), assume the input is h_1(y) = … = h_r(y) = 0 with deg h_j ≤ 2, y ∈ Q^k, and real zero set K(R) ⊂ [−R, R]^k. Let N = C(k+2, 2), and let m(y) = v₂(1, y) ∈ Q^N be the Veronese vector of all monomials y^γ with |γ| ≤ 2, where m_0 = 1 (constant monomial). Let H = {u ∈ Q^N : Σ_γ h_{j,γ} u_γ = 0 ∀j}. Then m(y) ∈ H ⟺ y ∈ K.

### 4.2 The space

A = B = Q^{2+N}, with index blocks {0}, {s}, {m_γ}. Write a = (a_0, a_s, a_m). The subspace V ⊂ A⊗B consists of the X = (X_{il}) satisfying:

- (E1) X_{s0} = X_{0s}
- (E2) X_{ss} − 2X_{00} = X_{m_0 m_0}
- (E3) X_{m_γ m_δ} = X_{m_δ m_γ}
- (E4) X_{m_γ m_δ} = X_{m_γ' m_δ'} whenever γ+δ = γ'+δ'
- (E5) Σ_γ h_{j,γ} X_{m_γ, 0} = 0 for each j

Marker vector: z = e_0⊗e_0.

### 4.3 Soundness: rational marker atoms are rational points of K

**Lemma 1.** Let a⊗b ∈ V with a, b rational and a_0 b_0 ≠ 0. Then y := (a_{m_{e_i}}/a_{m_0})_i ∈ K(Q).

*Proof.* Normalise a_0 = b_0 = 1 and write a = (1, s, u), b = (1, s', u').
- (E1) gives s = s'.
- (E2) gives u_0 u'_0 = s² − 2 ≠ 0, since s ∈ Q. So u, u' ≠ 0.
- (E3) says uu'^T = u'u^T, which forces u' = λu with λ ≠ 0.
- (E4) says u_γu_δ depends only on γ+δ. So m := u/u_0 satisfies m_α = m_{α−e_i} m_{e_i}, that is, m = v₂(1, y).
- (E5) says u_0 h_j(y) = 0. ∎

**Soundness.** Suppose range(ρ) ⊆ V and z^Tρz > 0. If ρ is Q-separable (or merely in the Q-span of rational product projectors in range ρ), then by (R) and (M) some rational product w ∈ V has a_0b_0 ≠ 0. Lemma 1 then gives K(Q) ≠ ∅. No compactness is used here.

### 4.4 The atoms

Fix y* ∈ K(Q) and m = m(y*). Every atom below lies in V; each was checked against E1 to E5.

- **K-atoms** κ(s, β) = (1, s, βm)⊗(1, s, β'm) with β' = (s²−2)/β. Use the six atoms (s, β) ∈ {0, ±2} × {±1}, with weight c = 2 for s = 0 and c = 1 for s = ±2. Let G(y*) = Σ c κκ^T.
- **√2-atoms** ω_± = (1, ±√2, 0)⊗(1, ±√2, 0). They lie in V_R: E2 holds because 2 − 2 = 0. Let R₀ = ω₊ω₊^T + ω₋ω₋^T, which is **rational**.
- **Free atoms** (a_0b_0 = 0). In each family the parameters are rational and dense, and no point of K is needed:
  - F1: (0, 0, u)⊗(1, s', 0) with u ∈ H.
  - F2: (1, s, 0)⊗(0, 0, u') with u' arbitrary.
  - F4: (0, 0, u)⊗(0, 1, 0) with u arbitrary.
  - F5: (0, s, μv₂(1,y))⊗(0, s', λμv₂(1,y)) with ss' = λμ² and **any** y ∈ Q^k. E5 is vacuous because b_0 = 0.

### 4.5 The identity

Write E00 = e₀e₀^T, Ess = e_se_s^T, S = e₀e_s^T + e_se₀^T, Ms = e_sm^T + me_s^T and N = mm^T, all on A or on B. Then aa^T = P(s) + βQ(s) + β²N, with P(s) = E00 + sS + s²Ess and Q(s) = (e₀m^T + me₀^T) + sMs. Average over β = ±1 (β' flips sign with β), so terms odd in β vanish. Then sum over s with the weights above. The M₀⊗M₀ terms cancel (−8 + 8), and the result is

G = 8E00⊗E00 + 16E00⊗Ess + 16Ess⊗E00 + 64Ess⊗Ess + 16S⊗S + (32E00 + 64Ess)⊗N + N⊗(8E00 + 16Ess) + 32Ms⊗Ms + 32N⊗N.

Also R₀ = 2Y⊗Y + 4S⊗S with Y = E00 + 2Ess. Hence

**D(y*) := 4R₀ − G(y*) = −32(Ess⊗Ess + Ms⊗Ms + N⊗N) − (32E00 + 64Ess)⊗N − N⊗(8E00 + 16Ess).**

Every term carrying the marker (E00⊗E00, E00⊗Ess, Ess⊗E00, S⊗S) cancels exactly. The row condition forced by (M) is met: ρz must be supplied by marker atoms, and the six K-atoms reproduce the √2-row 8(e₀⊗e₀ + 2e_s⊗e_s) independently of y*. That needs Σc s = Σc β = Σc sβ' = Σc(s²−2) = 0 and Σc s² = 2Σc, and the chosen weights satisfy all of these.

**D(y*) lies in the span Φ of free projectors whenever y* ∈ K(R).** F5 with y = y*, μ = 1, s' = 1, s = ±1 gives Σ_± ww^T = 2[(Ess⊗Ess + Ms⊗Ms + N⊗N) + Ess⊗N + N⊗Ess]. Here Ess⊗N lies in span F2, which is Sym(A_{0s})⊗Sym(B_m), and N⊗Ess lies in span F4. Next, E00⊗N ∈ span F2. Finally N⊗E00 ∈ span F1, which is Sym(H)⊗Sym(B_{0s}); this is exactly where m(y*) ∈ H, that is h(y*) = 0, is used.

### 4.6 Construction of ρ and completeness

1. Let Φ' = span F1 + span F2 + span F4 + span F5. Each family is the image of a polynomial map, so its span is computable by monomial expansion. Pick a finite set W₀ of rational free atoms spanning Φ' (for example, interpolation grids), and a basis W_b ⊆ W₀. Set F₀ = Σ_{w∈W₀} ww^T.
2. Fix a rational complement of Φ' and write D(y) = Σ_{w∈W_b} μ_w(y) ww^T + (complement part), with μ_w ∈ Q[y]. For y ∈ K(R) the complement part vanishes. Let B ∈ Q bound Σ|coeff(μ_w)|·max(1,R)^{deg} over all w, and set t = 1/B.
3. Output **ρ = 4tR₀ + F₀** (normalise the trace if desired).

ρ is rational and PSD, with range ⊆ V, since all atoms lie in V_R. Moreover z^Tρz = 4t·2 > 0, because free atoms contribute nothing at z. And ρ is **separable over R**, since 4tR₀ + F₀ is an explicit real decomposition.

*Completeness.* Let y* ∈ K(Q). Then ρ = tG(y*) + [F₀ + tD(y*)], and F₀ + tD(y*) = Σ_{W₀∖W_b} ww^T + Σ_{W_b}(1 + tμ_w(y*)) ww^T. Here |tμ_w(y*)| ≤ 1 by the box bound, so every coefficient is a nonnegative rational. G(y*) has rational atoms and rational weights. So ρ is Q-separable. ∎

*Upper bound (Q-SEP ≤_p HTP(Q)).* Suppose ρ = Σ λ_i P_i with rational product projectors P_i. The set {λ ≥ 0 : Σλ_iP_i = ρ} is a rational polyhedron, so it has a rational vertex with support ≤ dim Sym(A⊗B) =: L (Carathéodory). Hence ρ is Q-separable iff ∃ a_j, b_j ∈ Q^d (j ≤ L) with Σ_j (a_j⊗b_j)(a_j⊗b_j)^T = ρ, after absorbing weights by four squares (which multiplies L by 4). This is a polynomial system over Q of size poly(d). ∎

Together with Theorem A this proves Theorem B.

### 4.7 Cost

The ambient dimension is d = 2 + C(k+2, 2) with k = (#variables after the compact-quadratic normal form). W₀ and B come from polynomial-size linear algebra over Q, and B has polynomially many bits. I believe the whole reduction is polynomial time. I verified that it is computable; I did not audit the bit sizes line by line. **Claim: computable many-one, polynomial time very likely.**

## 7. Checked / assumed

| Item | Status |
|---|---|
| Theorem A (proof above) | checked by hand |
| Lemma 1 / soundness | checked |
| Membership of all atom families in V (E1–E5) | checked family by family |
| Identity D = 4R₀ − G (§4.5) | checked by hand twice, including the M₀⊗M₀ cancellation; **not machine-checked** (next step: 20-line exact-arithmetic C++ check with random y ∈ K) |
| D ∈ Φ' for y ∈ K(R) | checked |
| Completeness bound | checked |
| Upper bound | checked |
| Poly-time of the hard direction | sketched, not audited |
| Selmer local–global facts, Lagrange, Carathéodory, universal fixed-size Diophantine over Z | assumed classical |
| [BB], [Sun] | unrefereed; used only in conditional statements |
