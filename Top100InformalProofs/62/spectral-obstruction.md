# An explicit asymptotic restriction obstruction from Euclidean prices

The lower bound uses the named unrefereed flat theorem. The comparison is with the spectral functionals listed in the proof.

## Survivor A: an explicit asymptotic-restriction obstruction invisible to every previously known spectral point (any field)
**Theorem A.** Over every field, with H = Δ_abcd(2^83) ⊗ E_ac(2^14) ⊗ E_bd(2^14):
- H ≴ T^{⊗50}. That is, H^{⊗k} ≤ T^{⊗(50k+o(k))} fails, and also fails as a degeneration over the algebraic closure.
- Every flattening rank, every CVZ quantum functional (with any grouping), every Strassen support functional, every laminar quantum functional of Botero et al., and every Alman–Li–Pratt edge functional satisfies F(H) ≤ F(T)^50.

**Proof.**
- *Obstruction.* Take F_S on the square (Thm 1.1(1),(2)).
  - log F_S(H) = 83 + 14(|ac|+|bd|)/W = 83 + 14√2 = 102.80.
  - log F_S(U) = (|ab|+|cd|)/2 = 1, and the same for V. By additivity F_S(T) = 4, so log F_S(T^50) = 100.
  - Since 102.80 > 100, monotonicity and multiplicativity give the asymptotic statement. The closure lemma gives the degeneration statement.
- *Known points.* On 𝓗_4 each of these restricts to a laminar cut-mixture: singleton weights β_x (total 1−α) plus at most one 2|2 cut with weight α.
  - Two 2|2 cuts always cross.
  - Groupings Q_ij give the cuts ij|kl, {k}, {l}, which is laminar. ALP edge functionals are grouped 3-party points. Botero et al.'s points equal laminar quantum functionals on their robust semiring, which contains GHZ and wires and hence 𝓗_4.
  - Per copy, the H cut values are: singleton 1.94, ab|cd 2.22, ad|bc 2.22, ac|bd 1.66.
  - U has singleton 1, (0, 2, 2) on the three 2|2 cuts. V has singleton 1, (2, 0, 2).
  - On every laminar face we need log2(2^{u_θ}+2^{v_θ}) − h_θ ≥ 0. The singleton split is irrelevant because all singleton values are equal.
  - C++ check ([local reference omitted] α grid 10^-6, three faces): the minimum margin is +0.00268 per copy, at α = 0.415 on cut ab|cd. The function minus the line is convex, so the grid check is sound.
  - Flattenings in log2, H vs T^50: 97 ≤ 100, 111 ≤ 116.1, 83 ≤ 150.

**Design (why it works).** For θ in the cut simplex, L(θ) = h·θ − LSE_T(θ) is concave, so the separating set is convex. h is chosen tangent to LSE_T at the two laminar points θ_A, θ_B whose midpoint is the Crofton point θ_E. The gap is LSE(θ_A) − LSE(θ_E) = 2.0587 − 2. The optimum in this family is exponent ratio 1.0293; the integer instance gives 1.0280.

**Inputs.** Thm 1.1 for a planar 4-point set, which needs a spectral 2-flat (Thm flats, Parts II–III, NOT checked). Additivity and multiplicativity of F_S, from the definition. Closure lemma (checked; short). ALP's list of known 4-mode points (checked in their §3.2.2).

**Weakest link.** Thm flats, the non-constructive part. A secondary point: "no known point certifies" is relative to the literature as of Sept–Nov 2026 (ALP v2, Botero v2, SDW). A non-spectral argument for H ≴ T^50 could exist.

**Grochow-universe rank.** Not top 10; roughly top 40.
- It is the first explicit pair in the free semiring 𝓗_4 (tensor-network states with direct sums) where asymptotic restriction is decided by a non-laminar spectral point, over every field including F_2.
- It shows concretely that Q ∪ ALP ∪ Botero do not decide asymptotic restriction even on 𝓗_4. This gives an explicit witness to ALP's "genuinely new points needed" suspicion, which they proved only abstractly.
- It is a near-immediate corollary of Thm 1.1 (the paper's intro already notes that averaging crossing cuts fails), and it touches no named GQ/CGQTZ/GGPS question.
