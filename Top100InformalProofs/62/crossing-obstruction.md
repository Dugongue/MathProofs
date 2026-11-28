# A conditional obstruction to linear crossing weights

The proof uses OpenAI’s unrefereed shifted crossing theorem and the exact hypotheses on the functional stated below.

## Paper inputs used (and how far I checked them)

- **P1. Theorem crossing (shifted crossing), at δ = 0.** There is an ordinary-sum decomposition E_X(2^{nt}) ⊗ E_Y(2^{nu}) = T_+ + T_- over Z, valid over every field. T_+ has flattening rank ≤ 2^{n√(t²+u²)+o(n)} on X+Y+ | X−Y−, and T_- has the same bound on X+Y− | X−Y+.
  - I read the proof in crossing-appendix.tex: free-fermion locality (z−w)^L[Y_I, Y_J] = C_IJ δ, an energy-truncated factorization, Cauchy–Binet unimodularity, and log D(H) ~ c√H.
  - The structure and the counting are plausible. I did not re-verify the Wick-sign bookkeeping line by line.
  - **This is the weakest link of S3-A.**
- **P2. Theorem hilbert / Thm 1.1.** These give the Hilbert-space price system. H(T;x) is jointly convex in leg positions, 1-homogeneous, translation invariant and depends only on distances. δ(S) = W(S), with mean width normalized so that a segment has its length. I read the proof (Gaussian-frame concentration plus ultralimit). It rests on the existence of flats, which I have not checked (Parts II–III).
- **P3. Theorem geometry (CAT(0)) and the quadrilateral inequality (eq. cur-quad).** These are used only for the sharp form of S3-A.
- **Standard facts.** The 2-party asymptotic spectrum is {matrix rank}. Mean width is Minkowski-additive. Crofton: the hyperplane measure separating a finite set S equals W(S).

---

## Survivor S3-A: Pythagorean obstruction to crossing functionals

**Theorem A (elementary form; needs only P1).** Let c1 = {A,B}|{C,D} and c2 = {A,D}|{B,C} be two crossing bipartitions, as seen on four parties A, B, C, D taken from the four atoms; the number of parties k ≥ 4 is arbitrary. Let α, β > 0.

Over C, there is no functional g on k-party tensors with all of the following properties:
- (i) monotone under restriction, g(X+Y) ≤ g(X) + g(Y) for ordinary sums (in particular any subadditive monotone g), and submultiplicative;
- (ii) on the side wires: g(E_AD(q)), g(E_BC(q)) ≤ q^α and g(E_AB(q)), g(E_CD(q)) ≤ q^β;
- (iii) on the diagonal pair: g(E_AC(q) ⊗ E_BD(q')) ≥ (qq')^{α+β}.

Over any field, the same holds with "functional g" read as "spectral point", condition (iii) taken as given, and (ii) as stated.

**Corollary A1.** Let θ be a distribution whose support contains two crossing bipartitions and nothing else, θ = α c1 + β c2. Then there is no monotone, subadditive, submultiplicative g with F_θ ≤ g ≤ G_θ.
- Lower QF: F_θ(E_AC ⊗ E_BD) ≥ (qq')^{α+β} by additivity of marginal entropies.
- Gauge mean: G_θ(E_xy(q)) = q^{θ(sep x,y)}.
- In particular, no "crossing quantum functional" sandwiched between the lower QF and the gauge geometric mean exists, even as an upper functional.
- This is the crossing analogue of the question in Botero–Christandl–Fraser–Leigh–Nieuwboer 2604.18283 (existence of an extension with F_θ ≤ F ≤ F^θ, asked for laminar θ), answered negatively. BCFLN found that the CVZ upper QF for crossing θ is not even normalized; A1 says no repair can exist inside the G_θ envelope.

**Proof.** Put X = (A,C) with X+ = A, and Y = (B,D) with Y+ = B. Let Z_n = E_AC(2^{nt}) E_BD(2^{nu}) = T_+ + T_- as in P1 with δ = 0, and write R = 2^{n√S+o(n)} where S = t²+u².

*Bounding T_+.* T_+ = Σ_{k≤R} P_k(A,B) ⊗ Q_k(C,D). It is a restriction of E_AD(R) ⊗ E_AB(2^{nu}) ⊗ E_DC(2^{nt}):
- A applies e_k ⊗ e_β ↦ Σ_a P_k[a,β] e_a, and B keeps β;
- D applies e_k ⊗ e_γ ↦ Σ_d Q_k[γ,d] e_d, and C keeps γ.

So log g(T_+) ≤ n(α√S + β(t+u)) + o(n).

*Bounding T_-.* Symmetrically, T_- ≤ E_AB(R) ⊗ E_AD(2^{nu}) ⊗ E_BC(2^{nt}), so log g(T_-) ≤ n(β√S + α(t+u)) + o(n).

*Contradiction.* The sum is a restriction of the direct sum, so g(Z_n) ≤ g(T_+) + g(T_-). Condition (iii) gives log g(Z_n) ≥ n(α+β)(t+u). Dividing by n, we need α(t+u) ≤ α√S or β(t+u) ≤ β√S. Both fail, because √(t²+u²) < t+u. ∎

**Theorem A′ (sharp form; needs P3).** Every spectral point F, over any field, has a wire metric d_F(a,b) = log₂ F(E_ab(2)) that satisfies the CAT(0) quadrilateral inequality d(A,C)² + d(B,D)² ≤ d(A,B)² + d(B,C)² + d(C,D)² + d(D,A)².
- Hence F ≤ G_θ on the four side wires forces d(A,C)² + d(B,D)² ≤ 2(α²+β²), so min(d(A,C), d(B,D)) ≤ √(α²+β²) < α+β.
- The diagonal loss is Pythagorean, and it is attained (Theorem B).
- The quadrilateral inequality for spectral points is in the paper (intro, Hamming-square remark). What is new here is A1 and its reading for the quantum-functional programme.

**Extension (k = 4, θ on the three 2|2 cuts with weights a, b, c).** d_θ violates the quadrilateral inequality iff, for some labelling, ab > c² + c(a+b). So no spectral point has wire metric d_θ in that region.

---
