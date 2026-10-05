# LLQTW Problem 1.8: machine-checked solution (Lean 4)

**Claim.** We give a complete, machine-checked Lean 4 proof (Lean v4.33.0, Mathlib v4.33.0)
resolving Problem 1.8 of Li, Li, Qiao, Tao and Wang, *On the average-case complexity landscape for
Tensor-Isomorphism-complete problems over finite fields* (arXiv:2604.00591). The same result
answers Open Problem 4 of Chizewer, Everett, Mithal and Qiao (arXiv:2603.27128).

> Problem 1.8: "Devise average-case polynomial-time algorithms for 3-tensor isomorphism over
> finite fields under the orthogonal and unitary group actions."

## What is proved

There is a single fixed randomized machine (a Mathlib `Turing.TM2`-based coin machine), together
with constants c₀, C > 0 and a cutoff B₀, all chosen before the field and the dimensions. For every
finite field F, every tensor format a × b × c, and the action of either

- the orthogonal group O = {P : PᵀP = I} on each factor, or
- the unitary group U = {P : P*P = I} over F_{q²} on each factor,

the following hold, where A is uniformly random and B is arbitrary:

- **Zero error.** The machine never outputs a wrong answer. Whenever a polynomial-time recognizer
  accepts A, it decides whether A and B are isomorphic.
- **Polynomial time.** Its expected running time is polynomial in the input length,
  poly(abc · log q).
- **Density.** The recognizer accepts at least a c₀/q fraction of tensors A. When a, b, c ≥ 2, the
  rejected fraction is at most C(1 + log m)/√m, where m is the median dimension, and it accepts
  every A when m < B₀.
- **Invariance.** Acceptance is invariant under the group action.

Scope: the standard dot-product orthogonal group O (in characteristic 2, the bilinear dot-product
group) and the standard Hermitian unitary group. Over F_q with q odd and even dimension this O is
one of the two orthogonal types O^±; the other type and the characteristic-2 quadratic-form groups
are not covered by this statement.

The formal statement is in `Problem18-statement.lean`: 449 lines, `import Mathlib` only, sorry-free.
It ends with `def Claim : Prop := AllFormatRoot`. Every declaration in it is copied verbatim from the
proof sources. This was checked textually and by comparing kernel terms, and all 56 statement
constants are identical. (The docstring "UNPROVED:" on `AllFormatRoot` dates from 2026-09-30,
before the proof existed, and is kept verbatim.)

## Certification

- Theorem: `Mathproof.Problem18RootClosure20261004.allFormatRoot : AllFormatRoot`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only. No `sorry`, no `native_decide`, no
  custom axioms.
- Kernel replay: every constant in the dependency closure was re-checked by the Lean kernel in a
  fresh environment. Result: 35,192 constants OK, 0 failing, root accepted (2026-10-04).
- The proof comprises 1,743 Lean modules (about 316k lines). Their SHA-256 hashes are listed in
  `SOURCE-MANIFEST.txt`. The SHA-256 of that manifest is
  `3c9fd2ab5a90d4178232d81774d46f5aa951fcb94402059d4913561ae027e615`.
- SHA-256 of `Problem18-statement.lean`:
  `61dd22e340138ad12eee0d35a3f63c64c02c5777ef153ca2a279cae38c3c1bf4`.

The complete proof will be released as a single Mathlib-only file, `Problem18.lean`, once its
standalone compilation finishes. It can be checked against the manifest above.

## Credits

Built on Mathlib (Apache-2.0), including its Turing machine library (Mario Carneiro; Pim Spelier and
Daan van Gent). The proof also contains Apache-2.0-licensed material, adapted with credit, from:

- Formal Conjectures (Google DeepMind);
- CompPoly (Nethermind and contributors);
- the Lax proof archive (word RAM: Jan Dreier with Claude Fable 5; RAM↔TM: Szymon Toruńczyk with
  Codex 5.6);
- openai/ten-proofs;
- a function-field Riemann–Roch formalization by Guanghao Li (via Lean Pool);
- Tau Ceti;
- Michael Stoll's EllipticCurves;
- monlib4 (Monica Omar);
- the CFSG Bender–Suzuki project;
- Anthropic's FLT project.

Full notices are in the file headers.

Copyright (c) 2026 <AUTHOR NAME>. All rights reserved for original portions (no license granted at
this time). Third-party portions remain under their own Apache-2.0 license.
