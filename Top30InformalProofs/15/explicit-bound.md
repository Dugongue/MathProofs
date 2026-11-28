# An effective bound from the flat inequality

The explicit bound is conditional on the two named unrefereed inputs. Its range of validity is distinct from the range where it dominates a competing asymptotic bound.

## Statement

**Theorem B1.** Let K be any field. Then Hexagon's `Flat K` holds. Consequently, with c₀ = 1/1600² (all thresholds explicit):

1. If char K ≠ 2, every circuit computing PERM_m over K has more than 2^{(log₂m)^{4/3}/1600²} = m^{c₀(log₂m)^{1/3}} gates, for every m ≥ 2^{43,200}.
2. Every circuit computing HC_m over K has more than 2^{(log₂m)^{4/3}/1600²} gates, for every m ≥ 2^{15,901,400}.
3. Items 1 and 2 hold verbatim for **approximating (border) circuits** (`Approximates`, Laurent-series constants), with the same thresholds: `flat_rate_approx_complete` uses the same `rate_of_projection κ`.
4. The same holds for every GridComplete family with blow-up κ, for m ≥ 2^{200(κ+3)³}.

This is, to our knowledge, the first superpolynomial general-circuit lower bound for PERM/HC with **both the constant and the threshold explicit**.
- Hexagon alone has an ineffective m₀ (its contracting branch).
- OpenAI's 11-24 circuit paper has the stronger exp(c(log N)²/(log log N)²), but states "c absolute, N₀(χ) depending on the characteristic" with no explicit value. Its proof passes through compactness and ultralimits.
- OpenAI's 11-23 no-shortening branch is effective, but in its own model and at exponent 5/4.

## Proof

1. **Definition match.** OpenAI's spectral points (Thm 1.1(2); §1 "A spectral point …") are nonnegative functions on tensors at a finite site set S. They are monotone under restrictions (local linear maps at each site), multiplicative under tensor products, additive under direct sums, with F(0) = 0 and F(1) = 1.
   - Every such F is a Hexagon spectral point (Spec, Ov/Core/Tensor.lean:101). A sum of restrictions of b_1..b_r is a restriction of ⊕b_k: concatenate the local maps, and the direct sum is block-diagonal. So F(s) ≤ F(⊕b_k) = ΣF(b_k). Multiplicativity and F(1) = 1 match.
   - "Group the indices at each site, adjoin a 1-dimensional factor at unused sites" is Hexagon's `push` and party set. (The same check is R-W4-A1 step 1.)

2. **Euclidean metric is a price.**
   - Take a finite set S ⊂ ℝ^k of positive diameter. OpenAI Thm 1.1(1),(2) give F_S with W(S)·log₂F_S(wire(2,u,v)) = |u−v|. So F_S.e(u,v) = |u−v|/W(S), and |u−v| = W(S)·F_S.e ∈ specCone K S ⊆ Prices K S.
   - For a map E : V → ℝ^k from a finite set V (CaseOne allows non-injective E), use `Spec.pull` along E onto S = E(V). Then `pull_e` gives exactly dist(E a, E b) as a price on V.
   - Diameter 0 gives the zero function, which lies in the cone (c = 0).
   - Hence `CaseOne K`, i.e. `Flat K` (Paper/Alternative.lean:41).

3. **Apply Hexagon's flat branch.**
   - `thm_flat_rate hK h2` (char ≠ 2) and `flat_rate_complete 40 … (gridComplete_hc K)` give the bounds, with m₀ the witness 2^{200(κ+3)³} in `rate_of_projection` (κ = 3 for PERM via `Paper/Grids.lean:59`, κ = 40 for HC). This gives 200·6³ = 43,200 and 200·43³ = 15,901,400.
   - The border version is `flat_rate_approx_complete`, with the same `rate_of_projection κ`.
   - The exponent identity m^{c₀(log m)^{1/3}} = 2^{(log m)^{4/3}/1600²} is `beyond_of_rate`. ∎

## Dependencies (flag every unverified input)

| Input | Status |
|---|---|
| Hexagon flat branch, explicit m₀ | Lean-verified (anthropics/formal-math/vp-vnp, CI green). Statements read in Rate.lean:337–341, 411–424 and Approximate.lean:229–238 |
| OpenAI Thm 1.1 / 1.2 (Euclidean prices / spectral flats over every field) | **CLAIMED, AI-written, no human check.** The scope doc lean/docs/379.md says "Lean constructs prices for tensors whose indices lie at sites in Euclidean space of any finite dimension". **I did not locate an unconditional Lean theorem in a 15-minute search.** Several companion Lean files (CompanionGeometry.lean:30, CharacteristicAlternative.lean:74/111, ChordGraph/*) still case-split on `Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin D)))`. Paper proof: Thm 1.2 by contradiction over finite prime fields (§16), plus field transfer (Lemma 7.1), plus ultralimits |
| Definition match (Strassen point ⇒ Hexagon gauge point; site grouping = push) | Elementary (above). A Lean bridge would need a definitional translation between `RankFunctional`/`SpectralPlacementPrices` (OpenAI, Lean 4.34.1) and `Ov.Spec` (Hexagon, Lean 4.33.1) |

**Lean plan (optional, CLAUDE.md rules).** Once OpenAI's unconditional existence theorem is located:
- (a) state the bridge `∀ K, Flat K` as a cited axiom over Hexagon's definitions;
- (b) prove PERM/HC explicit bounds from `thm_flat_rate` / `flat_rate_complete` with `m₀ := 2^{200(κ+3)^3}`. This needs a variant of `rate_of_projection` exposing its witness, since the Lean statement hides it under ∃. That is a 5-line restatement.

Toolchain gap: 4.34.1 vs 4.33.1, so use the bridge policy (as for NavierStokesAndEuler).
