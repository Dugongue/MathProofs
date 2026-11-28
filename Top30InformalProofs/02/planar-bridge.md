# The planar bound used in Liu’s sum-of-squares bridge

The transfer uses the unrefereed flat inequality. Liu’s preprint is available [here](https://hexagonmath.org/pdf/2611.00994v1).

## Objects (all checked in source)
- **Liu's hypothesis** (2611.00994 §2, verbatim model, citing O-Nov-23 Def 2.1):
  - work over K̄;
  - terminals sit at e1, e2, −e1, −e2;
  - C_r = [a=c][b=d], with r bits per terminal;
  - networks use bit cables of cost (bits × length), arbitrary tables, and free local operations at terminals;
  - a strict shortening is C_r = Σ_{a≤A} N_a, with each cost(N_a) ≤ w and w + 4·log₂A < 4r.
  - Liu reduces closure to exact himself: C_r^{⊗q} = C_{qr} is a sum of poly(q)·A^q networks of cost ≤ qw. The hypothesis Liu needs is therefore "no exact strict shortening over K̄, for any r".
  - For the R(q) corollary he needs K = ℂ.
- **Lean** ([local reference omitted]):
  - `HasSpectralFlat F d := Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin d)))` (Hierarchy/FlatPrices.lean:13).
  - The structure fields (LinearAlgebra/SpectralBooks/SpectralSpace.lean:48) are `zero_tensor`, `collapsed`, `group` (compatibility across site sets, with trivial slots at empty fibres), `wire` (price of the binary diagonal at x0, x1 = dist), `transport`, `dist_le_diagonal`, and `normalized`.
  - `normalized` says: for each injective placement x : I ↪ X there is φ ∈ normalizedSpectrum (f0 = 0, f1 = 1, additive, multiplicative, monotone under restriction) with price T x = price(diag_I) x · log₂ φ(T).
  - `prime_flats : ∀ p prime, ∃ᶠ D, HasSpectralFlat (ZMod p) D` (Hierarchy/PrimeFlats.lean:15).
  - `UnboundedPrimeFieldFlats.all_dimensions h F d : HasSpectralFlat F d` for every field F (PaperBounds.lean:14), via `HasSpectralFlat.of_prime_fields`. Char 0 goes through the ultraproduct `of_prime_fields_charZero` (FlatFieldTransfer.lean:74).
  - So the Lean gives HasSpectralFlat ℂ 2 and HasSpectralFlat F̄_p 2 directly.
  - A grep for `sorry`/`admit`/`axiom` in Hierarchy/ and SpectralBooks/ finds no real hits (only an identifier named `admit` and docstrings). We have not built the tree or run axiom checks.

## The proof (exact model, any A)
Fix P a price system on ℝ² over K. Let Pt = {±e1, ±e2} be the terminal set, c = price(diag_Pt) > 0 (`diagonal_pos`), and φ the spectral point for Pt.

1. **price(C_r on Pt) = 4r.** C_r is the tensor product of r wires e1↔−e1 and r wires e2↔−e2, grouped at Pt. Since φ is multiplicative, price is additive on ⊗. Each wire grouped at Pt prices at dist (`wire` + `group`), so the total is r·2 + r·2.
2. **price(N_a on Pt) ≤ cost(N_a), with arbitrary internal sites.**
   - Pad N_a to S_a = Pt ∪ nodes; `group` leaves the price unchanged.
   - On S_a, N_a is a restriction of ⊗(cables): at each site, contract with the node table.
   - Use the spectral point for S_a: log φ_{S_a}(N_a) ≤ Σ log φ_{S_a}(cable). Multiplying by c_{S_a} > 0 gives price ≤ Σ cable prices = Σ bits·length = cost. Same-site cables cost 0 (`collapsed`).
   - Node positions are irrelevant. Even "nodes outside the disk" would not matter.
3. **Sum rule.** Σ_a N_a is the image of ⊕_a N_a under the sum map at each terminal, so it is a restriction of ⊕_a N_a. Additivity plus monotonicity give φ(C_r) ≤ A·max_a φ(N_a), hence 4r ≤ max price(N_a) + c·log₂A ≤ w + c·log₂A.
4. **c ≤ 4.**
   - `diagonal_mono` gives diag(Pt) ≤ diag(Pt ∪ {0}).
   - `transport` plus `collapsed` give the star bound diag(I) ≤ Σ_j dist(e_j, e_i) at any i ∈ I. This is the private `scale_upper` (FlatFieldTransfer.lean:63).
   - Taking i = 0 gives 4.
   - (oaG's mean-width law would give c = W(square) = 2√2. The `flatDiagonalLaw_*` lemmas need the extra hypothesis `JointlyConvexDiagonal`, which is not part of HasSpectralFlat. It is not needed here.)
5. Hence w + 4·log₂A ≥ 4r for every exact decomposition. **No strict shortening exists, for any r, any A, over any K with HasSpectralFlat K 2.** Liu's closure-to-exact step then gives 4r ≤ w + 4·log₂A + O(log q)/q → 4r ≤ w + 4·log₂A, which also kills the closure version.

The A ≥ 2 case (L1's "open" case) is exactly step 3. A spectral point turns a sum of A alternatives into a log₂A additive penalty, scaled by the diagonal price c ≤ 4. This is the 4 in Def 2.1. OpenAI's 2D·log₂A threshold is precisely the star bound, and that is not a coincidence.
