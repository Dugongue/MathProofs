# Two regimes for parabolic tensor isomorphism

These are sufficient conditions for each tier over a fixed finite field. Intermediate block sizes remain open.

## 1. Setting

Fix a finite field F = F_q, presented over F_p. CGQTZ fix the field, so q is a constant below unless stated otherwise.

For a full or partial flag F of F^n, let P_F be its stabilizer. Let b(F) be the largest step dimension. By "the five actions" of a family G we mean X_G for X ∈ {(i), …, (v)} (CGQTZ Def. 1.6). For actions (iii) and (iv), P^{-t} of a block-upper-triangular matrix is block-lower-triangular. Reversing the basis in those modes makes it upper again, and PARABOLIC.md allows mixed orientations.

## 2. Theorem L (Levi dichotomy for parabolic families over a fixed finite field)

Let (F_n) be flags with largest step b_n, and let G_n = P_{F_n}. For each of the five actions:

**(a) Hard side.** If b_n ≥ n^ε for some ε > 0, then X_{P_F} is TI-complete.
- **Hardness.** The Levi factor of P_F contains GL_b acting on the step block B, written in the adapted basis. Every diag(1, …, g, …, 1) preserves both B and the span U′ of the other basis vectors. So the step block gives a GL-Levi section in the sense of `IsLeviSection`, with m = b ≥ n^ε. Theorem S then gives TI_b ≤ X_P, and padding TI_n into TI_{n^{1/ε}} gives TI ≤ X_P.
- **Membership.** For maximal flags this is TIPar (Lean). For general flags, flag preservation is k unary linear relations (`blockTriangular_iff_forall_preserves`), and the marker compilation (Borel = 1 marker on End(U), 09-12 §8) gives X_P ≤ TI.

**(b) Easy side.** If b_n ≤ c·√(log n), then X_{P_F} ∈ P.
- PARABOLIC.md with s ≤ |GL_b(F_q)| < q^{b²} = n^{O(c² log q)} gives this. The diagonal-subgroup forms needed for actions (ii)–(v) are subgroups of the product of three parabolics, which that theorem allows.

**(c) In between.** For √(log n) ≪ b ≪ n^{o(1)} the complexity is sandwiched between two bounds:
- **Lower:** TI at side b reduces to X_P, by Theorem S.
- **Upper:** X_P is decidable in time poly(L)·q^{b²}.

So **the complexity of parabolic TI is governed by the largest Levi block alone**: hard as soon as that block is polynomial, polynomial when it is at most √(log n), and in between it scales like TI at side b.

## 3. Corollaries a reader of CGQTZ will care about

**C1. Borel TI is in P.** Over a fixed finite field, isomorphism of 3-tensors under Borel subgroups is decidable in deterministic polynomial time, for all five actions. This is (b) with b = 1, and it includes canonical stabilizer generators.
- In CGQTZ's notation, TI_B ⊆ P.
- It answers the Borel case of the research direction stated after Theorem 1.12, §1.5: "TI_G for … special linear, affine, and Borel or parabolic subgroups".

**C2. TI does not reduce to TI_Borel unless TI ∈ P.** The open item "TI ≤ TI_B" in our 09-12 ledger is therefore **settled negatively, conditionally**: a reduction would put TI in P, contradicting the standard belief and every cryptographic use (MEDS, ALTEQ). Unconditionally, padding cannot do it (`flag_cut_blocks_lift`), and now no method can unless TI ∈ P.

**C3. The 09-12 Borel route to OQ 1.9 is dead.** That route needs TI_SL ≤ TI_{B∩SL}.
- B∩SL is solvable, with diagonal block images inside F_q^*, so s ≤ q − 1. PARABOLIC.md decides B∩SL-transporters, including the prescribed determinant triple, in polynomial time. So TI_{B∩SL} ∈ P.
- Since TI ≤ TI_SL (Lean, 09-02), the link would give TI ∈ P.
- **The rule this gives:** any route to TI_SL ≤ TI must avoid solvable intermediate groups. This complements the determinant-rigidifier threshold (Theorem D).

**C4. The §1.5 list, complete except for one arrow.**

| Group family (CGQTZ §1.5) | TI-hard | ≤ TI | Status |
|---|---|---|---|
| SL | yes (Theorem S; Lean `JouxNarayanan54`, `ti_class_le_tiSL_class`) | **open** (Q7.2) | the remaining arrow |
| affine | yes (Theorem S) | yes (repo AffineTensorIsomorphism) | = TI |
| parabolic, Levi block ≥ n^ε | yes (Theorem L(a)) | yes (markers) | = TI |
| parabolic, Levi block ≤ √(log n) | — | yes | **∈ P** (Theorem L(b)) |
| Borel | no unless TI ∈ P | yes | **∈ P** (C1) |
| Siegel parabolic (Sp ∩ Stab(Lagrangian)) | yes (`ti_class_le_tiSiegel_class`) | open (`OPEN_tiSiegel_le_ti`) | Levi = GL_n via hypLift, so hard |

**C5. Fixed-arity reduction for every Levi-section form group.**
- If G preserves poly-time-constructible forms and has a polynomial GL-Levi section (Sp, split O, Hermitian U over F_{q²}, O over fields of level ≤ 2, O(p,q) with q ≥ m^ε), then d-tensor G-isomorphism reduces to 3-tensor G-isomorphism.
- *Proof:* d-Tensor G-Iso ≤ d-TI_GL by FGS form compilation (the d-ary analogue of CGQTZ Thm 1.10, which uses only bounded-arity linear structures). Then d-TI ≤ 3-TI by Grochow–Qiao Theorem B, and 3-TI ≤ 3-TI_G by Theorem S.
- This extends CGQTZ Theorem 1.13, proved there only for O(ℝ) and U(ℂ), to all these families. For Sp it repeats the archive's Corollary 2.
