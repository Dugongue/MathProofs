# Localization and directional tensor isomorphism

Let \(B\) be ordinary ternary three-tensor isomorphism. For a finite-field tensor comparison \(x\), write \(A_\alpha(x)\) for existence of a transporter with the prescribed determinant tuple \(\alpha\). Four constructions extend the earlier Boolean-difference and fixed-localization theorems. The suggested ranks are editorial insertions into the Grochow list. [Earlier directional and localization theorems](prior/transfer.md)

## Suggested rank 2. A programmable localization spectrum for one all-locally-isomorphic pair

One ordinary free tensor pair over \(\mathbb Z[t]\) can realize the truth table of a supplied monotone span program as the subset of listed irreducible factors that are inverted varies. Additional program bits can be arbitrary independent ordinary ternary TI queries. Every upward-closed family is realizable from its explicit minimal sets. Every produced pair is isomorphic at every prime localization, over every finite quotient, and over the profinite completion. On the formula-annotated family, choosing at most \(k\) factors to repair the pair is NP-complete, and counting successful subsets is \(\#\mathrm P\)-complete under polynomial-time Turing reductions. [Proof and complexity scope](spectrum.md)

## Suggested rank 3. An integral symplectic conjugacy defect with identical split group types

Given two ordinary TI queries \(x,y\), construct one pair of smooth connected closed subgroup schemes inside a common \(\mathrm{Sp}_{6d}\), both of split type \(\mathbb G_m\times\mathbb G_a^{2d}\). The pair is conjugate over \(\mathbb Z\) exactly when \(B(x)\) and \(B(y)\), and over \(\mathbb Z[1/2]\) exactly when \(B(x)\). It is conjugate over every prime localization of \(\mathbb Z\), every \(\mathbb Z_\ell\), and over \(\mathbb Q\) and \(\mathbb R\). The same reduction also works for spaces of symmetric bilinear forms under symplectic congruence, with the same unimodular hyperbolic form in both spaces. [Exact tensor-to-symplectic carrier](structure.md)

## Suggested rank 4. One Laurent variable suffices for two independent signed tests

For independent comparisons \(x,y\) over any two explicitly presented finite fields, one ordinary tensor pair over the fixed ring \(\mathbb Z[t]\) is isomorphic exactly when \(A_\alpha(x)\land A_\beta(y)\). The same pair over \(\mathbb Z[t,t^{-1}]\) tests \(A_\alpha(x)\). Every height-one localization and the fraction field sees an isomorphism. All prime localizations, all finite quotients, and the profinite completion each detect only ordinary isomorphism of the first input. Dimension two is minimal for this construction model with a fixed finite-type characteristic-zero ring and arbitrary finite-field residue quotients. [Proof and size bounds](arithmetic.md)

## Suggested rank 7. Exact signed witness counts from residues of global ordinary transporters

For each precision \(3^k\), take the finite image of the global ordinary transporter set under the explicit coordinate observation of the arithmetic carrier. Its cardinality over \(\mathbb Z\), divided by an explicit calibration factor, is the number of signed ternary transporters with the prescribed determinants. Over \(\mathbb Z[1/2]\) the same relaxed-pin observations recover the ordinary count. The calibration includes the rank of the simultaneous infinitesimal action and takes account of the extra last digit visible in a divided graph block. For the plain compiled tensor with the fixed observation mask, the calibration factors are four times explicitly given powers of three. [Counting theorem and observation model](complexity.md)

## Verification

The four reductions and counting arguments are written proofs. Lean independently checks the unit-selection product identities for the first construction. Finite tests cover the CRT selectors, all 168 upward-closed families on four selection bits, and the small congruence-image counts. [Lean source](LocalizationSpectrum.lean) · [Finite controls](spectrum_controls.py) · [Verification](Verification.json)
