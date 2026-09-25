import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Matrix.PosDef

/-!
# Arbitrary-rank four-measurement selected-sum lower bound and equality rigidity

Let P, Q, R, T be any four n-outcome projective measurements on C^D,
with n >= 2 and D > 0. Outcome ranks are arbitrary, including zero.
Let lambda be the largest real root of

  t^4 - 4*t^3 + 6*(n-1)/n*t^2
    - 4*(n-1)*(n-2)/n^2*t + (n-1)*(n-2)*(n-3)/n^3.

Some selected sum P_a + Q_b + R_c + T_e has operator norm >= lambda.
If all selected sums have norm <= lambda, every subtriple is an algebraic
3-fold unbiased measurement: it satisfies the pairwise unbiasedness and
anchored triple-product identities stated in `FourMeas.IsThreeUM`.
Neither equal ranks nor any initial unbiasedness assumption is required.

This proves the four-measurement, arbitrary-outcome-rank extension of
Theorem 9 in Sebastien Designolle and Mate Farkas,
"k-fold unbiased measurements and maximal incompatibility",
arXiv:2609.20728v1, Section V.1 and Appendix D.
The paper proves the rank-one bound for arbitrary numbers of measurements,
and its arbitrary-rank extension for pairs, triples, and two-outcome tuples;
the arbitrary-rank four-measurement case with more outcomes is left open.
This does not settle the extension for all numbers of measurements or the
dimension-six MUB existence problem.

The proof uses a cubic harmonic-mean test, exact trace moments through
degree seven, and a coercive defect inequality. All supporting definitions
and proofs are included here. Only Mathlib modules are imported.

Main theorems:
* `four_measurement_arbitrary_rank`
* `four_measurement_arbitrary_rank_rigidity`
* `FourMeas.quantitative_Phi`
-/

section
section

open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.style.haveILetI false

namespace MUMSpectral

abbrev Mat (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

structure PVM (n D : ℕ) where
  proj : Fin n → Mat D
  isProj : ∀ a, IsStarProjection (proj a)
  orthogonal : ∀ a b, a ≠ b → proj a * proj b = 0
  complete : ∑ a, proj a = 1

def Unbiased {n D : ℕ} (P Q : PVM n D) : Prop :=
  (∀ a b, P.proj a * Q.proj b * P.proj a = (n : ℝ)⁻¹ • P.proj a) ∧
  (∀ a b, Q.proj b * P.proj a * Q.proj b = (n : ℝ)⁻¹ • Q.proj b)

theorem PVM.proj_nonneg {n D : ℕ} (P : PVM n D) (a : Fin n) : 0 ≤ P.proj a :=
  (P.isProj a).nonneg

theorem PVM.sum_proj_mul {n D : ℕ} (P : PVM n D) (X : Mat D) :
    ∑ a, P.proj a * X = X := by
  rw [← Finset.sum_mul, P.complete, one_mul]

theorem PVM.sum_mul_proj {n D : ℕ} (P : PVM n D) (X : Mat D) :
    ∑ a, X * P.proj a = X := by
  rw [← Finset.mul_sum, P.complete, mul_one]

theorem Unbiased.symm {n D : ℕ} {P Q : PVM n D} (h : Unbiased P Q) :
    Unbiased Q P := ⟨fun b a => h.2 a b, fun b a => h.1 a b⟩

noncomputable def matTrace {D : ℕ} (A : Mat D) : ℝ := (Matrix.trace A).re

noncomputable def cubic (n : ℕ) (t : ℝ) : ℝ :=
  t^3 - 3*t^2 + (3*((n:ℝ)-1)/(n:ℝ))*t -
    ((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2

noncomputable def quartic (n : ℕ) (t : ℝ) : ℝ :=
  t^4 - 4*t^3 + (6*((n:ℝ)-1)/(n:ℝ))*t^2 -
    (4*((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2)*t +
    ((n:ℝ)-1)*((n:ℝ)-2)*((n:ℝ)-3)/(n:ℝ)^3

def LargestRoot (n : ℕ) (lam : ℝ) : Prop :=
  IsGreatest {t : ℝ | quartic n t = 0} lam

noncomputable def defect {n D : ℕ} (P Q R : PVM n D)
    (a b c : Fin n) : Mat D :=
  P.proj a * (Q.proj b * R.proj c + R.proj c * Q.proj b) * P.proj a -
    (2/(n:ℝ)^2) • P.proj a

noncomputable def defectSquares {n D : ℕ} (P Q R : PVM n D) : Mat D :=
  ∑ a, ∑ b, ∑ c, (defect P Q R a b c)^2

noncomputable def cycle {n D : ℕ} (P Q R : PVM n D) : Mat D :=
  ∑ a, ∑ b, ∑ c, P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c

noncomputable def centeredCycle {n D : ℕ} (P Q R : PVM n D) : Mat D :=
  cycle P Q R - ((2-(n:ℝ))/(n:ℝ)^2) • (1 : Mat D)

noncomputable def cycleDefect {n D : ℕ} (P Q R : PVM n D) : Mat D :=
  centeredCycle P Q R + star (centeredCycle P Q R) +
  centeredCycle Q R P + star (centeredCycle Q R P) +
  centeredCycle R P Q + star (centeredCycle R P Q)

noncomputable def selectedSum {n D : ℕ} (P Q R T : PVM n D)
    (a b c d : Fin n) : Mat D := P.proj a + Q.proj b + R.proj c + T.proj d

def FourSettingLowerBound : Prop :=
  ∀ (n D : ℕ), 2 ≤ n → 0 < D →
  ∀ (P Q R T : PVM n D), Unbiased P Q → Unbiased Q R → Unbiased R P →
  ∀ lam : ℝ, LargestRoot n lam →
    ∃ a b c d : Fin n, lam ≤ ‖selectedSum P Q R T a b c d‖

end MUMSpectral

namespace MUMSpectral

section Algebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

theorem defect_mul_expansion (p q r : A) (t : ℝ)
    (hqpq : q * p * q = t • q) (hrqr : r * q * r = t • r) :
    (p * (q*r+r*q) * p - (2*t^2) • p) * (q*r) =
      p*q*r*p*q*r + t^2 • (p*r) - (2*t^2) • (p*q*r) := by
  have hmid : p*r*(q*p*q)*r = t^2 • (p*r) := by
    rw [hqpq]
    simp only [mul_smul_comm, smul_mul_assoc]
    rw [show p*r*q*r = p*(r*q*r) by noncomm_ring, hrqr]
    simp [mul_smul_comm, smul_smul, pow_two]
  calc
    _ = p*q*r*p*q*r + p*r*(q*p*q)*r - (2*t^2) • (p*q*r) := by
      simp only [add_mul, mul_add, sub_mul, smul_mul_assoc]
      noncomm_ring
    _ = _ := by rw [hmid]

end Algebra

section StarRing
variable {A : Type*} [Ring A] [StarRing A]

theorem real_part_square_identity (d : A) :
    (d + star d)^2 + (d-star d)*star (d-star d) =
      2 • (d*star d + star d*d) := by
  simp only [star_sub, star_star, two_nsmul]
  noncomm_ring

theorem three_square_identity (a b c : A) :
    3 • (a^2+b^2+c^2) - (a+b+c)^2 =
      (a-b)^2 + (a-c)^2 + (b-c)^2 := by
  rw [show (3 : ℕ) = 2+1 from rfl, add_nsmul, two_nsmul, one_nsmul]
  noncomm_ring

end StarRing
end MUMSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem matrix_trace_mono {A B : M} (h : A ≤ B) :
    (Matrix.trace A).re ≤ (Matrix.trace B).re := by
  have hp : (B-A).PosSemidef := h
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  rw [Matrix.trace_sub, Complex.sub_re] at ht
  exact sub_nonneg.mp ht

theorem matrix_trace_product_nonneg {A B : M}
    (hA : 0 ≤ A) (hB : 0 ≤ B) : 0 ≤ (Matrix.trace (A*B)).re := by
  obtain ⟨K, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA
  have hp : (K * B * star K).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.nonneg_iff_posSemidef.mp hB).mul_mul_conjTranspose_same K
  have ht := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  rw [Matrix.trace_mul_cycle] at ht
  exact ht

theorem matrix_inverse_antitone {A B : M}
    (hA : A.PosDef) (hB : B.PosDef) (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
  exact CStarAlgebra.antitoneOn_ringInverse
    ⟨hA.posSemidef.nonneg, hA.isUnit⟩ ⟨hB.posSemidef.nonneg, hB.isUnit⟩ h

theorem real_part_square_le (d : M) :
    (d+star d)^2 ≤ 2 • (d*star d+star d*d) := by
  have h : 0 ≤ (d-star d)*star (d-star d) := mul_star_self_nonneg _
  calc
    (d+star d)^2 ≤ (d+star d)^2+(d-star d)*star (d-star d) := le_add_of_nonneg_right h
    _ = 2 • (d*star d+star d*d) := by
      simp only [star_sub, star_star, two_nsmul]
      noncomm_ring

theorem three_selfadjoint_square_le (a b c : M)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : IsSelfAdjoint c) :
    (a+b+c)^2 ≤ 3 • (a^2+b^2+c^2) := by
  have h : 0 ≤ (a-b)^2+(a-c)^2+(b-c)^2 :=
    add_nonneg (add_nonneg (ha.sub hb).sq_nonneg (ha.sub hc).sq_nonneg)
      (hb.sub hc).sq_nonneg
  apply sub_nonneg.mp
  rw [show (3 : ℕ) = 2+1 from rfl, add_nsmul, two_nsmul, one_nsmul]
  convert h using 1 <;> noncomm_ring

end MUMSpectral

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem projection_sandwich_le (x q : M) (hq : IsStarProjection q) :
    x*q*star x ≤ x*star x := by
  have h := star_right_conjugate_nonneg hq.one_sub.nonneg x
  apply sub_nonneg.mp
  simpa only [mul_sub, sub_mul, mul_one] using h

theorem orthogonal_row_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q x : ι → M) (hq : ∀ i, IsStarProjection (q i))
    (horth : ∀ i j, i ≠ j → q i*q j=0) :
    (∑ i, x i*q i)*star (∑ i, x i*q i) ≤ ∑ i, x i*star (x i) := by
  have hmul (i j : ι) : x i*q i*star (x j*q j) =
      if i=j then x i*q i*star (x i) else 0 := by
    rw [star_mul, (hq j).isSelfAdjoint.star_eq]
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      calc
        x i*q i*(q i*star (x i)) = x i*(q i*q i)*star (x i) := by noncomm_ring
        _ = x i*q i*star (x i) := by rw [(hq i).isIdempotentElem]
    · rw [if_neg hij]
      calc
        x i*q i*(q j*star (x j)) = x i*(q i*q j)*star (x j) := by noncomm_ring
        _ = 0 := by rw [horth i j hij]; simp
  have heq : (∑ i, x i*q i)*star (∑ i, x i*q i) =
      ∑ i, x i*q i*star (x i) := by
    rw [star_sum, Finset.sum_mul]
    simp_rw [Finset.mul_sum, hmul]
    simp
  rw [heq]
  exact Finset.sum_le_sum fun i _ => projection_sandwich_le (x i) (q i) (hq i)

end MUMSpectral

open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem projection_cover_trace_bound {ι : Type*} [Fintype ι]
    (p : ι → M) (hp : ∀ i, IsStarProjection (p i))
    (hcomplete : ∑ i, p i = 1) (H : M) (t : ℝ)
    (hH : ∀ i, t • p i ≤ H) : t*(D:ℝ) ≤ (Matrix.trace H).re := by
  have hterm (i : ι) : t*(Matrix.trace (p i)).re ≤ (Matrix.trace (p i*H)).re := by
    have hs := star_left_conjugate_nonneg (sub_nonneg.mpr (hH i)) (p i)
    rw [(hp i).isSelfAdjoint.star_eq] at hs
    have ht := (Complex.nonneg_iff.mp
      (Matrix.nonneg_iff_posSemidef.mp hs).trace_nonneg).1
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
      (hp i).isIdempotentElem, Matrix.trace_sub, Matrix.trace_smul,
      Complex.sub_re, Complex.smul_re, smul_eq_mul] at ht
    rw [Matrix.trace_mul_cycle, (hp i).isIdempotentElem] at ht
    rw [(hp i).isIdempotentElem] at ht
    exact sub_nonneg.mp ht
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simp only [← Finset.mul_sum, ← Complex.re_sum, ← Matrix.trace_sum,
    ← Finset.sum_mul, hcomplete, one_mul, Matrix.trace_one, Fintype.card_fin,
    Complex.natCast_re] at hsum
  exact hsum

end MUMSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem posDef_of_scalar_lower {A : M} {g : ℝ} (hg : 0 < g)
    (h : g • (1:M) ≤ A) : A.PosDef := by
  have hp := (Matrix.PosDef.one.smul hg).add_posSemidef (show (A-g • (1:M)).PosSemidef from h)
  simpa only [add_sub_cancel] using hp

theorem scalar_matrix_inverse {g : ℝ} (hg : g ≠ 0) :
    (g • (1:M))⁻¹ = g⁻¹ • (1:M) := by
  apply Matrix.inv_eq_right_inv
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul, inv_mul_cancel₀ hg, one_smul]

theorem inverse_le_of_scalar_lower {A : M} {g : ℝ} (hg : 0 < g)
    (h : g • (1:M) ≤ A) : A⁻¹ ≤ g⁻¹ • (1:M) := by
  have hA := posDef_of_scalar_lower hg h
  have hgI : (g • (1:M)).PosDef := Matrix.PosDef.one.smul hg
  have hi : A⁻¹ ≤ (g • (1:M))⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
    exact CStarAlgebra.antitoneOn_ringInverse
      ⟨hgI.posSemidef.nonneg, hgI.isUnit⟩ ⟨hA.posSemidef.nonneg, hA.isUnit⟩ h
  rwa [scalar_matrix_inverse hg.ne'] at hi

end MUMSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MUMSpectral

theorem right_inverse_quadratic {A : Type*} [Ring A] (x y : A)
    (h : (1+x)*y=1) : y=1-x+x^2*y := by
  symm
  calc
    1-x+x^2*y = (1+x)*y-x+x^2*y := by rw [h]
    _ = y+x*((1+x)*y-1) := by noncomm_ring
    _ = y := by rw [h]; simp

variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem matrix_inverse_quadratic (X : M) (hX : (1+X).PosDef) :
    (1+X)⁻¹ = 1-X+X^2*(1+X)⁻¹ := by
  apply right_inverse_quadratic
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit)

theorem matrix_inverse_trace_quadratic (F : M) (k : ℝ)
    (hX : (1+k • F).PosDef) :
    (Matrix.trace ((1+k • F)⁻¹)).re =
      (D:ℝ)-k*(Matrix.trace F).re +
        k^2*(Matrix.trace (F^2*(1+k • F)⁻¹)).re := by
  conv_lhs => rw [matrix_inverse_quadratic (k • F) hX]
  have hpow : (k • F)^2 = k^2 • F^2 := by
    simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [hpow]
  simp only [smul_mul_assoc, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Complex.add_re, Complex.sub_re,
    Complex.smul_re, Complex.natCast_re, smul_eq_mul]

end MUMSpectral

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem commute_matrix_inverse_right {A B : M} (h : Commute A B)
    (hB : IsUnit B) : Commute A B⁻¹ := by
  obtain ⟨u, rfl⟩ := hB
  simpa only [Matrix.coe_units_inv] using h.units_inv_right

theorem resolvent_remainder_nonneg (S B : M) (lam : ℝ)
    (hS : 0 ≤ S) (hB : IsSelfAdjoint B) (hBS : Commute B S)
    (hres : (lam • (1:M)-S).PosDef) :
    0 ≤ (lam • (1:M)-S)⁻¹ * (S*B^2) := by
  have hSA : Commute S (lam • (1:M)-S) := by
    change S*(lam • (1:M)-S)=(lam • (1:M)-S)*S
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  have hBA : Commute B (lam • (1:M)-S) := by
    change B*(lam • (1:M)-S)=(lam • (1:M)-S)*B
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, hBS.eq]
  have hSR := commute_matrix_inverse_right hSA hres.isUnit
  have hBR := commute_matrix_inverse_right hBA hres.isUnit
  have hprod : 0 ≤ S*B^2 := (hBS.symm.pow_right 2).mul_nonneg hS hB.sq_nonneg
  have hR : 0 ≤ (lam • (1:M)-S)⁻¹ := hres.inv.posSemidef.nonneg
  exact (hSR.symm.mul_right (hBR.symm.pow_right 2)).mul_nonneg hR hprod

end MUMSpectral

namespace MUMSpectral
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem trace_product_mono {A B C : M} (hA : 0 ≤ A) (hBC : B ≤ C) :
    (Matrix.trace (A*B)).re ≤ (Matrix.trace (A*C)).re := by
  have h := matrix_trace_product_nonneg hA (sub_nonneg.mpr hBC)
  simpa only [mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

theorem inverse_trace_deficit (F : M) (k L c : ℝ)
    (hF : IsSelfAdjoint F) (hk : 0 ≤ k) (hg : 0 < 1-k*L)
    (hlower : -(L • (1:M)) ≤ F)
    (hquad : (Matrix.trace (F^2)).re ≤ c*(Matrix.trace F).re) :
    (Matrix.trace ((1+k • F)⁻¹)).re ≤
      (D:ℝ)-k*(1-c*k/(1-k*L))*(Matrix.trace F).re := by
  have hx : (1-k*L) • (1:M) ≤ 1+k • F := by
    have hh := smul_le_smul_of_nonneg_left hlower hk
    calc
      (1-k*L) • (1:M) = 1+k • (-(L • (1:M))) := by
        simp only [sub_eq_add_neg, add_smul, neg_smul, one_smul, smul_neg, smul_smul]
      _ ≤ 1+k • F := add_le_add le_rfl hh
  have hpd := posDef_of_scalar_lower hg hx
  have hi := inverse_le_of_scalar_lower hg hx
  have ht := trace_product_mono hF.sq_nonneg hi
  simp only [mul_smul_comm, mul_one, Matrix.trace_smul, Complex.smul_re,
    smul_eq_mul] at ht
  have ht2 := mul_le_mul_of_nonneg_left hquad (le_of_lt (inv_pos.mpr hg))
  rw [matrix_inverse_trace_quadratic F k hpd]
  have ht3 := mul_le_mul_of_nonneg_left (ht.trans ht2) (sq_nonneg k)
  calc
    (D:ℝ)-k*(Matrix.trace F).re + k^2*(Matrix.trace (F^2*(1+k • F)⁻¹)).re
      ≤ (D:ℝ)-k*(Matrix.trace F).re +
        k^2*((1-k*L)⁻¹*(c*(Matrix.trace F).re)) := add_le_add le_rfl ht3
    _ = (D:ℝ)-k*(1-c*k/(1-k*L))*(Matrix.trace F).re := by
      rw [div_eq_mul_inv]
      ring

noncomputable def matrixAverage {ι : Type*} [Fintype ι] (A : ι → M) : M :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, A i

theorem matrixAverage_const {ι : Type*} [Fintype ι] [Nonempty ι] (A : M) :
    matrixAverage (fun _ : ι => A) = A := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [matrixAverage, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem matrixAverage_mono {ι : Type*} [Fintype ι]
    {A B : ι → M} (h : ∀ i, A i ≤ B i) : matrixAverage A ≤ matrixAverage B := by
  apply smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun i _ => h i)
  positivity

theorem matrixAverage_posDef {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → M) (hA : ∀ i, (A i).PosDef) : (matrixAverage A).PosDef := by
  apply Matrix.PosDef.smul
  · exact Matrix.posDef_sum Finset.univ_nonempty fun i _ => hA i
  · exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem harmonic_mean_lower {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → M) (B : M) (hA : ∀ i, (A i).PosDef) (hB : B.PosDef)
    (h : ∀ i, B ≤ A i) : B ≤ (matrixAverage fun i => (A i)⁻¹)⁻¹ := by
  have hmean := matrixAverage_posDef (fun i => (A i)⁻¹) (fun i => (hA i).inv)
  have havg : (matrixAverage fun i => (A i)⁻¹) ≤ B⁻¹ := by
    calc
      _ ≤ matrixAverage (fun _ : ι => B⁻¹) :=
        matrixAverage_mono (fun i => matrix_inverse_antitone hB (hA i) (h i))
      _ = B⁻¹ := matrixAverage_const _
  have hinv := matrix_inverse_antitone hmean hB.inv havg
  simpa only [Matrix.nonsing_inv_nonsing_inv B
    ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)] using hinv

theorem resolvent_polynomial_minorant (S B H : M) (lam w : ℝ)
    (hS : 0 ≤ S) (hB : IsSelfAdjoint B) (hBS : Commute B S)
    (hres : (lam • (1:M)-S).PosDef) (hw : 0 < w)
    (hidentity : (lam • (1:M)-S)*H = 1-w⁻¹ • (S*B^2)) :
    H ≤ (lam • (1:M)-S)⁻¹ := by
  let A := lam • (1:M)-S
  have hRA : A⁻¹*A=1 :=
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp hres.isUnit)
  have heq : H=A⁻¹-w⁻¹ • (A⁻¹*(S*B^2)) := by
    calc
      H = A⁻¹*(A*H) := by rw [← mul_assoc, hRA, one_mul]
      _ = A⁻¹*(1-w⁻¹ • (S*B^2)) := by rw [hidentity]
      _ = _ := by rw [mul_sub, mul_one, mul_smul_comm]
  have hp : 0 ≤ w⁻¹ • (A⁻¹*(S*B^2)) :=
    smul_nonneg (le_of_lt (inv_pos.mpr hw))
      (resolvent_remainder_nonneg S B lam hS hB hBS hres)
  change H ≤ A⁻¹
  rw [heq]
  exact sub_le_self _ hp

end MUMSpectral

namespace MUMSpectral
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {D : ℕ}
local notation "M" => Mat D

theorem trace_realpart_square_le (A V : M) (h : A*star A ≤ V) :
    (Matrix.trace ((A+star A)^2)).re ≤ 4*(Matrix.trace V).re := by
  have h1 := matrix_trace_mono (real_part_square_le A)
  have h2 := matrix_trace_mono h
  have hcyc : Matrix.trace (star A*A)=Matrix.trace (A*star A) := Matrix.trace_mul_comm _ _
  simp only [two_nsmul, Matrix.trace_add, Complex.add_re, hcyc] at h1
  linarith

theorem trace_three_realparts_square_le (A B C VA VB VC : M)
    (hA : A*star A ≤ VA) (hB : B*star B ≤ VB) (hC : C*star C ≤ VC) :
    (Matrix.trace (((A+star A)+(B+star B)+(C+star C))^2)).re ≤
      12*((Matrix.trace VA).re+(Matrix.trace VB).re+(Matrix.trace VC).re) := by
  have hsa (X : M) : IsSelfAdjoint (X+star X) := by
    change star (X+star X)=X+star X
    simp only [star_add, star_star, add_comm]
  have h1 := matrix_trace_mono (three_selfadjoint_square_le
    (A+star A) (B+star B) (C+star C) (hsa A) (hsa B) (hsa C))
  have h2 := trace_realpart_square_le A VA hA
  have h3 := trace_realpart_square_le B VB hB
  have h4 := trace_realpart_square_le C VC hC
  rw [show (3:ℕ)=2+1 from rfl, add_nsmul, two_nsmul, one_nsmul] at h1
  simp only [Matrix.trace_add, Complex.add_re] at h1
  linarith

theorem resolvent_dominates_positive_summand (S P : M) (lam eps : ℝ)
    (hS : 0 ≤ S) (hP : 0 ≤ P) (hnorm : ‖S+P‖ ≤ lam-eps) :
    P+eps • (1:M) ≤ lam • (1:M)-S := by
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap (S+P)
    ((norm_nonneg _).trans hnorm) (add_nonneg hS hP)).mp hnorm
  rw [Algebra.algebraMap_eq_smul_one] at h
  apply sub_nonneg.mp
  convert sub_nonneg.mpr h using 1 <;> module

theorem finite_uniform_gap {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ) (lam : ℝ) (h : ∀ i, f i < lam) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ i, f i ≤ lam-eps := by
  classical
  let m := Finset.univ.sup' Finset.univ_nonempty f
  have hm : m < lam := (Finset.sup'_lt_iff _).mpr (fun i _ => h i)
  refine ⟨lam-m, sub_pos.mpr hm, fun i => ?_⟩
  have hi : f i ≤ m := Finset.le_sup' f (Finset.mem_univ i)
  linarith

theorem selected_norm_of_harmonic_trace {ι : Type*} [Fintype ι] [Nonempty ι]
    {n : ℕ} (hn : 0 < n) (hD : 0 < D) (S : ι → M) (P : PVM n D)
    (lam : ℝ) (hS : ∀ i, 0 ≤ S i)
    (htrace : (∀ i, (lam • (1:M)-S i).PosDef) →
      (Matrix.trace ((matrixAverage fun i => (lam • (1:M)-S i)⁻¹)⁻¹)).re ≤ (D:ℝ)) :
    ∃ i j, lam ≤ ‖S i+P.proj j‖ := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  by_contra! hnone
  obtain ⟨eps, heps, hgap⟩ := finite_uniform_gap
    (fun ij : ι × Fin n => ‖S ij.1+P.proj ij.2‖) lam (fun ij => hnone ij.1 ij.2)
  let A : ι → M := fun i => lam • (1:M)-S i
  have hdom (i : ι) (j : Fin n) : P.proj j+eps • (1:M) ≤ A i :=
    resolvent_dominates_positive_summand (S i) (P.proj j) lam eps
      (hS i) (P.proj_nonneg j) (hgap (i,j))
  have hA (i : ι) : (A i).PosDef := by
    apply posDef_of_scalar_lower heps
    exact (le_add_of_nonneg_left (P.proj_nonneg (0:Fin n))).trans (hdom i 0)
  let H := (matrixAverage fun i => (A i)⁻¹)⁻¹
  have hH (j : Fin n) : (1+eps) • P.proj j ≤ H := by
    have hpd : (P.proj j+eps • (1:M)).PosDef := by
      simpa only [add_comm] using
        (Matrix.PosDef.one.smul heps).add_posSemidef
          (Matrix.nonneg_iff_posSemidef.mp (P.proj_nonneg j))
    have hpi : P.proj j ≤ 1 := sub_nonneg.mp (P.isProj j).one_sub.nonneg
    calc
      (1+eps) • P.proj j = P.proj j+eps • P.proj j := by module
      _ ≤ P.proj j+eps • (1:M) :=
        add_le_add le_rfl (smul_le_smul_of_nonneg_left hpi heps.le)
      _ ≤ H := harmonic_mean_lower A _ hA hpd (fun i => hdom i j)
  have hlo := projection_cover_trace_bound P.proj P.isProj P.complete H (1+eps) hH
  have hhi := htrace hA
  have hDr : (0:ℝ) < D := by exact_mod_cast hD
  change (Matrix.trace H).re ≤ (D:ℝ) at hhi
  nlinarith

end MUMSpectral

namespace MUMSpectral
variable {D : ℕ}
local notation "M" => Mat D
theorem frame_product_row {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → M) (Y : κ → M)
    (hX : ∑ i, X i*star (X i)=1) (hY : ∑ j, Y j*star (Y j)=1) :
    ∑ ij : ι × κ, (X ij.1*Y ij.2)*star (X ij.1*Y ij.2)=1 := by
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ i, X i*(∑ j, Y j*star (Y j))*star (X i) := by
      simp only [Finset.mul_sum, Finset.sum_mul, star_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      noncomm_ring
    _ = 1 := by simpa only [hY, mul_one] using hX

theorem frame_product_column {ι κ : Type*} [Fintype ι] [Fintype κ]
    (X : ι → M) (Y : κ → M)
    (hX : ∑ i, star (X i)*X i=1) (hY : ∑ j, star (Y j)*Y j=1) :
    ∑ ij : ι × κ, star (X ij.1*Y ij.2)*(X ij.1*Y ij.2)=1 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    _ = ∑ j, star (Y j)*(∑ i, star (X i)*X i)*Y j := by
      simp only [Finset.mul_sum, Finset.sum_mul, star_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = 1 := by simpa only [hX, mul_one] using hY

theorem PVM.frame_row {n : ℕ} (P : PVM n D) :
    ∑ a, P.proj a*star (P.proj a)=1 := by
  have hi (a : Fin n) : P.proj a*P.proj a=P.proj a := (P.isProj a).isIdempotentElem
  simpa only [(P.isProj _).isSelfAdjoint.star_eq, hi] using P.complete

theorem PVM.frame_column {n : ℕ} (P : PVM n D) :
    ∑ a, star (P.proj a)*P.proj a=1 := by
  have hi (a : Fin n) : P.proj a*P.proj a=P.proj a := (P.isProj a).isIdempotentElem
  simpa only [(P.isProj _).isSelfAdjoint.star_eq, hi] using P.complete

theorem frame_cycle_lower {ι : Type*} [Fintype ι] (X : ι → M)
    (hrow : ∑ i, X i*star (X i)=1)
    (hcol : ∑ i, star (X i)*X i=1) :
    -((2:ℝ) • (1:M)) ≤ (∑ i, (X i)^2)+star (∑ i, (X i)^2) := by
  have hp : 0 ≤ ∑ i, (X i+star (X i))*star (X i+star (X i)) :=
    Finset.sum_nonneg fun i _ => mul_star_self_nonneg _
  have heq : (∑ i, (X i+star (X i))*star (X i+star (X i))) =
      (∑ i, (X i)^2)+star (∑ i, (X i)^2)+(2:ℝ) • (1:M) := by
    simp only [star_add, star_star, add_mul, mul_add, Finset.sum_add_distrib,
      star_sum, star_pow, pow_two, star_mul, hrow, hcol]
    simp only [two_smul]
    abel
  rw [heq] at hp
  exact neg_le_iff_add_nonneg.mpr hp

theorem cycle_real_lower {n : ℕ} (P Q R : PVM n D) :
    -((2:ℝ) • (1:M)) ≤ cycle P Q R + star (cycle P Q R) := by
  let Y : Fin n × Fin n → M := fun bc => Q.proj bc.1*R.proj bc.2
  let X : Fin n × (Fin n × Fin n) → M := fun abc => P.proj abc.1*Y abc.2
  have hyrow : ∑ bc, Y bc*star (Y bc)=1 :=
    frame_product_row Q.proj R.proj Q.frame_row R.frame_row
  have hycol : ∑ bc, star (Y bc)*Y bc=1 :=
    frame_product_column Q.proj R.proj Q.frame_column R.frame_column
  have hxrow : ∑ abc, X abc*star (X abc)=1 :=
    frame_product_row P.proj Y P.frame_row hyrow
  have hxcol : ∑ abc, star (X abc)*X abc=1 :=
    frame_product_column P.proj Y P.frame_column hycol
  simpa only [X, Y, Fintype.sum_prod_type, pow_two, cycle, mul_assoc] using
    frame_cycle_lower X hxrow hxcol

theorem centeredCycle_real_lower {n : ℕ} (P Q R : PVM n D) :
    -((2*(1+(2-(n:ℝ))/(n:ℝ)^2)) • (1:M)) ≤
      centeredCycle P Q R + star (centeredCycle P Q R) := by
  have h := sub_nonneg.mpr (cycle_real_lower P Q R)
  apply sub_nonneg.mp
  convert h using 1
  simp only [centeredCycle, star_sub, star_smul, star_one, star_trivial]
  module

theorem cycleDefect_lower_exact {n : ℕ} (P Q R : PVM n D) :
    -((6*(1+(2-(n:ℝ))/(n:ℝ)^2)) • (1:M)) ≤ cycleDefect P Q R := by
  have h := add_le_add (add_le_add (centeredCycle_real_lower P Q R)
    (centeredCycle_real_lower Q R P)) (centeredCycle_real_lower R P Q)
  convert h using 1 <;> (try dsimp only [cycleDefect]) <;> module

theorem defect_selfAdjoint {n : ℕ} (P Q R : PVM n D) (a b c : Fin n) :
    IsSelfAdjoint (defect P Q R a b c) := by
  change star (defect P Q R a b c)=defect P Q R a b c
  simp only [defect, star_sub, star_mul, star_add, star_smul, star_trivial,
    (P.isProj a).isSelfAdjoint.star_eq, (Q.isProj b).isSelfAdjoint.star_eq,
    (R.isProj c).isSelfAdjoint.star_eq]
  noncomm_ring

theorem defect_left_supported {n : ℕ} (P Q R : PVM n D) (a b c : Fin n) :
    P.proj a*defect P Q R a b c=defect P Q R a b c := by
  simp only [defect, mul_sub, mul_smul_comm]
  rw [← mul_assoc, ← mul_assoc, (P.isProj a).isIdempotentElem]

theorem defect_right_supported {n : ℕ} (P Q R : PVM n D) (a b c : Fin n) :
    defect P Q R a b c*P.proj a=defect P Q R a b c := by
  have h := congrArg star (defect_left_supported P Q R a b c)
  simpa only [star_mul, (P.isProj a).isSelfAdjoint.star_eq,
    (defect_selfAdjoint P Q R a b c).star_eq] using h

theorem orthogonal_supported_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p e : ι → M) (horth : ∀ i j, i ≠ j → p i*p j=0)
    (he : ∀ i, IsSelfAdjoint (e i))
    (hl : ∀ i, p i*e i=e i) (hr : ∀ i, e i*p i=e i) :
    (∑ i, e i)*star (∑ i, e i)=∑ i, (e i)^2 := by
  have hmul (i j : ι) : e i*e j=if i=j then (e i)^2 else 0 := by
    by_cases hij : i=j
    · subst j
      simp [pow_two]
    · rw [if_neg hij]
      calc
        e i*e j = (e i*p i)*(p j*e j) := by rw [hl, hr]
        _ = e i*(p i*p j)*e j := by noncomm_ring
        _ = 0 := by rw [horth i j hij]; simp
  rw [star_sum, Finset.sum_mul]
  simp_rw [(he _).star_eq, Finset.mul_sum, hmul]
  simp

noncomputable def contractedDefect {n : ℕ} (P Q R : PVM n D) : M :=
  ∑ c, (∑ b, (∑ a, defect P Q R a b c)*Q.proj b)*R.proj c

theorem contractedDefect_bound {n : ℕ} (P Q R : PVM n D) :
    contractedDefect P Q R*star (contractedDefect P Q R) ≤ defectSquares P Q R := by
  let X : Fin n → Fin n → M := fun b c => ∑ a, defect P Q R a b c
  let Y : Fin n → M := fun c => ∑ b, X b c*Q.proj b
  have hx (b c : Fin n) : X b c*star (X b c)=∑ a, (defect P Q R a b c)^2 :=
    orthogonal_supported_sum_square P.proj (fun a => defect P Q R a b c)
      P.orthogonal (fun a => defect_selfAdjoint P Q R a b c)
      (fun a => defect_left_supported P Q R a b c)
      (fun a => defect_right_supported P Q R a b c)
  calc
    contractedDefect P Q R*star (contractedDefect P Q R)
      ≤ ∑ c, Y c*star (Y c) :=
        orthogonal_row_contraction R.proj Y R.isProj R.orthogonal
    _ ≤ ∑ c, ∑ b, X b c*star (X b c) := Finset.sum_le_sum fun c _ =>
      orthogonal_row_contraction Q.proj (fun b => X b c) Q.isProj Q.orthogonal
    _ = ∑ c, ∑ b, ∑ a, (defect P Q R a b c)^2 := by simp_rw [hx]
    _ = defectSquares P Q R := by
      unfold defectSquares
      rw [Finset.sum_comm]
      conv_lhs =>
        arg 2
        intro b
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

end MUMSpectral
namespace MUMSpectral
variable {n D : ℕ}
local notation "M" => Mat D

theorem contractedDefect_expanded (P Q R : PVM n D) :
    contractedDefect P Q R = ∑ a, ∑ b, ∑ c, defect P Q R a b c*(Q.proj b*R.proj c) := by
  unfold contractedDefect
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    intro b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem sum_projector_triples (P Q R : PVM n D) :
    (∑ a, ∑ b, ∑ c, P.proj a*Q.proj b*R.proj c) = 1 := by
  simp_rw [PVM.sum_mul_proj]
  exact P.complete

theorem sum_projector_pairs_repeated (P R : PVM n D) :
    (∑ a, ∑ _b : Fin n, ∑ c, P.proj a*R.proj c) = (n:ℝ) • (1:M) := by
  simp_rw [PVM.sum_mul_proj]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, P.complete, Nat.cast_smul_eq_nsmul]

theorem contractedDefect_eq_centeredCycle (P Q R : PVM n D)
    (hn : 0 < n) (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    contractedDefect P Q R=centeredCycle P Q R := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hc : 2/(n:ℝ)^2 = 2*((n:ℝ)⁻¹)^2 := by simp [div_eq_mul_inv, inv_pow]
  have hpoint (a b c : Fin n) :
      defect P Q R a b c*(Q.proj b*R.proj c) =
      P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c +
      ((n:ℝ)⁻¹)^2 • (P.proj a*R.proj c) -
      (2*((n:ℝ)⁻¹)^2) • (P.proj a*Q.proj b*R.proj c) := by
    simpa only [defect, hc] using defect_mul_expansion
      (P.proj a) (Q.proj b) (R.proj c) (n:ℝ)⁻¹ (hPQ.2 a b) (hQR.2 b c)
  rw [contractedDefect_expanded]
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [sum_projector_triples, sum_projector_pairs_repeated]
  change cycle P Q R + ((n:ℝ)⁻¹)^2 • ((n:ℝ) • (1:M)) -
    (2*((n:ℝ)⁻¹)^2) • (1:M) = centeredCycle P Q R
  unfold centeredCycle
  have hs : ((n:ℝ)⁻¹)^2*(n:ℝ)-2*((n:ℝ)⁻¹)^2 = -((2-(n:ℝ))/(n:ℝ)^2) := by
    field_simp
    ring
  simp only [smul_smul]
  rw [add_sub_assoc, ← sub_smul, hs, neg_smul, sub_eq_add_neg]
  simp only [sub_eq_add_neg]

end MUMSpectral

namespace MUMSpectral
open scoped BigOperators

private theorem aux1_trace_defect_square {D : ℕ} (p x : Mat D) (u : ℝ)
    (hpp : p*p=p) :
    Matrix.trace ((p*x*p-u•p)^2) =
      Matrix.trace ((p*x*p-u•p)*x-u•(p*x*p-u•p)) := by
  let d := p*x*p-u•p
  have hdp : d*p=d := by
    dsimp [d]
    simp only [sub_mul, smul_mul_assoc, mul_assoc, hpp]
  have hpd : p*d=d := by
    dsimp [d]
    simp only [mul_sub, mul_smul_comm]
    simp only [← mul_assoc, hpp]
  change Matrix.trace (d^2) = Matrix.trace (d*x-u•d)
  calc
    _ = Matrix.trace (d*(p*x*p-u•p)) := by rw [pow_two]
    _ = Matrix.trace (d*p*x*p)-u•Matrix.trace d := by
      simp only [mul_sub, mul_smul_comm, ← mul_assoc, hdp,
        Matrix.trace_sub, Matrix.trace_smul]
    _ = Matrix.trace (d*x)-u•Matrix.trace d := by
      rw [hdp, Matrix.trace_mul_comm (d*x) p, ← mul_assoc, hpd]
    _ = _ := by simp only [Matrix.trace_sub, Matrix.trace_smul]

private theorem aux2_sum_defect_zero {n D : ℕ} (hn : 0<n) (P Q R : PVM n D) :
    (∑ a, ∑ b, ∑ c, defect P Q R a b c)=0 := by
  have hnr : (n:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hsum : (∑ a, ∑ b, ∑ c,
      P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a) = (2:ℝ)•(1:Mat D) := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib]
    simp only [← Finset.sum_mul, ← Finset.mul_sum, R.complete, Q.complete,
      mul_one, one_mul]
    simp only [fun a => (P.isProj a).isIdempotentElem.eq]
    rw [← Finset.sum_add_distrib]
    simp [← two_smul ℝ, ← Finset.smul_sum, P.complete]
  simp only [defect, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.smul_sum, P.complete]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hc : (n:ℝ)*((n:ℝ)*(2/(n:ℝ)^2))=2 := by field_simp
  rw [hc, sub_self]

theorem sum_defect_mul_cycle {n D : ℕ} (hn : 0<n) (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    (∑ a, ∑ b, ∑ c, defect P Q R a b c * (Q.proj b*R.proj c)) =
      centeredCycle P Q R := by
  have ht : 2/(n:ℝ)^2=2*((n:ℝ)⁻¹)^2 := by simp [div_eq_mul_inv, inv_pow]
  have hp (a b c : Fin n) := defect_mul_expansion (P.proj a) (Q.proj b)
    (R.proj c) (n:ℝ)⁻¹ (hPQ.2 a b) (hQR.2 b c)
  simp only [defect, ht]
  simp_rw [hp]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  have hs1 : (∑ a : Fin n, ∑ b : Fin n, ∑ c : Fin n, P.proj a * R.proj c) = (n:ℝ)•(1:Mat D) := by
    simp only [← Finset.mul_sum, R.complete, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, ← Finset.smul_sum, P.complete,
      Nat.cast_smul_eq_nsmul]
  have hs2 : (∑ a, ∑ b, ∑ c, P.proj a * Q.proj b * R.proj c) = (1:Mat D) := by
    simp only [← Finset.mul_sum, R.complete, Q.complete, P.complete, mul_one]
  rw [hs1, hs2, smul_smul]
  change cycle P Q R + _ - _ = cycle P Q R - _
  rw [add_sub_assoc, ← sub_smul]
  have hc : ((n:ℝ)⁻¹)^2*(n:ℝ)-2*((n:ℝ)⁻¹)^2 = -((2-(n:ℝ))/(n:ℝ)^2) := by
    simp only [div_eq_mul_inv, inv_pow]; ring
  simp only [hc, neg_smul, sub_eq_add_neg]

theorem defect_isSelfAdjoint {n D : ℕ} (P Q R : PVM n D) (a b c : Fin n) :
    IsSelfAdjoint (defect P Q R a b c) := by
  change star (defect P Q R a b c) = _
  simp only [defect, star_sub, star_mul, star_add, star_smul, star_trivial,
    (P.isProj a).isSelfAdjoint.star_eq, (Q.isProj b).isSelfAdjoint.star_eq,
    (R.isProj c).isSelfAdjoint.star_eq]
  noncomm_ring

theorem trace_defect_reverse {n D : ℕ} (P Q R : PVM n D) (a b c : Fin n) :
    Matrix.trace (defect P Q R a b c * (R.proj c*Q.proj b)) =
      star (Matrix.trace (defect P Q R a b c * (Q.proj b*R.proj c))) := by
  rw [← Matrix.trace_conjTranspose]
  change _ = Matrix.trace (star (defect P Q R a b c * (Q.proj b*R.proj c)))
  rw [star_mul, star_mul, (defect_isSelfAdjoint P Q R a b c).star_eq,
    (Q.isProj b).isSelfAdjoint.star_eq, (R.isProj c).isSelfAdjoint.star_eq,
    Matrix.trace_mul_comm]

theorem trace_defectSquares_centeredCycle {n D : ℕ} (hn : 0<n)
    (P Q R : PVM n D) (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    matTrace (defectSquares P Q R) =
      matTrace (centeredCycle P Q R + star (centeredCycle P Q R)) := by
  have hp (a b c : Fin n) :
      Matrix.trace ((defect P Q R a b c)^2) =
      Matrix.trace (defect P Q R a b c*(Q.proj b*R.proj c)) +
      star (Matrix.trace (defect P Q R a b c*(Q.proj b*R.proj c))) -
      (2/(n:ℝ)^2)•Matrix.trace (defect P Q R a b c) := by
    have h := aux1_trace_defect_square (P.proj a) (Q.proj b*R.proj c+R.proj c*Q.proj b)
      (2/(n:ℝ)^2) (P.isProj a).isIdempotentElem.eq
    change Matrix.trace ((defect P Q R a b c)^2) =
      Matrix.trace (defect P Q R a b c*(Q.proj b*R.proj c+R.proj c*Q.proj b)-
        (2/(n:ℝ)^2)•defect P Q R a b c) at h
    rw [h, mul_add, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
      trace_defect_reverse]
  have hs : Matrix.trace (defectSquares P Q R) =
      Matrix.trace (centeredCycle P Q R)+star (Matrix.trace (centeredCycle P Q R)) := by
    simp only [defectSquares, Matrix.trace_sum]
    simp_rw [hp]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← star_sum,
      ← Finset.smul_sum, ← Matrix.trace_sum]
    rw [sum_defect_mul_cycle hn P Q R hPQ hQR, aux2_sum_defect_zero hn P Q R,
      Matrix.trace_zero, smul_zero, sub_zero]
  unfold matTrace
  rw [hs, Matrix.trace_add]
  change _ = (Matrix.trace (centeredCycle P Q R)+Matrix.trace (centeredCycle P Q R)ᴴ).re
  rw [Matrix.trace_conjTranspose]

theorem trace_cycle_cyclic {n D : ℕ} (P Q R : PVM n D) :
    Matrix.trace (cycle P Q R)=Matrix.trace (cycle Q R P) := by
  have hp (a b c : Fin n) :
      Matrix.trace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c) =
      Matrix.trace (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*P.proj a) := by
    rw [show P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c =
      P.proj a*(Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c) by noncomm_ring,
      Matrix.trace_mul_comm]
  simp only [cycle, Matrix.trace_sum]
  simp_rw [hp]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

theorem matTrace_centeredCycle_cyclic {n D : ℕ} (P Q R : PVM n D) :
    matTrace (centeredCycle P Q R + star (centeredCycle P Q R)) =
    matTrace (centeredCycle Q R P + star (centeredCycle Q R P)) := by
  unfold matTrace
  simp only [Matrix.trace_add]
  change (Matrix.trace (centeredCycle P Q R)+Matrix.trace (centeredCycle P Q R)ᴴ).re =
    (Matrix.trace (centeredCycle Q R P)+Matrix.trace (centeredCycle Q R P)ᴴ).re
  simp only [Matrix.trace_conjTranspose, centeredCycle, Matrix.trace_sub]
  rw [trace_cycle_cyclic P Q R]

theorem trace_cycleDefect_eq_three_defectSquares {n D : ℕ} (hn : 0<n)
    (P Q R : PVM n D) (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    matTrace (cycleDefect P Q R) = 3*matTrace (defectSquares P Q R) := by
  have h1 := matTrace_centeredCycle_cyclic P Q R
  have h2 := matTrace_centeredCycle_cyclic Q R P
  have h3 := trace_defectSquares_centeredCycle hn P Q R hPQ hQR
  have hadd : matTrace (cycleDefect P Q R) =
      matTrace (centeredCycle P Q R+star (centeredCycle P Q R))+
      matTrace (centeredCycle Q R P+star (centeredCycle Q R P))+
      matTrace (centeredCycle R P Q+star (centeredCycle R P Q)) := by
    simp only [cycleDefect, matTrace, Matrix.trace_add, Complex.add_re]
    ring
  rw [hadd]
  linarith

end MUMSpectral

open scoped BigOperators
namespace MUMMoments
variable {A : Type*} [Ring A] [Algebra ℝ A]
variable {n : ℕ}

noncomputable def sum3 (f : Fin n → Fin n → Fin n → A) : A := ∑ a, ∑ b, ∑ c, f a b c

theorem sum3_bac (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f b a c) = sum3 f := by
  exact Finset.sum_comm

theorem sum3_acb (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f a c b) = sum3 f := by
  unfold sum3
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

theorem sum3_bca (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f b c a) = sum3 f := by
  unfold sum3
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  exact Finset.sum_comm

theorem sum3_cab (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f c a b) = sum3 f := by
  calc
    _ = sum3 (fun a b c => f b c a) := sum3_bca _
    _ = sum3 f := sum3_bca _

theorem sum3_cba (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f c b a) = sum3 f := by
  calc
    _ = sum3 (fun a b c => f b c a) := sum3_acb _
    _ = sum3 f := sum3_bca _

theorem sum3_add (f g : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => f a b c + g a b c) = sum3 f + sum3 g := by
  simp only [sum3, Finset.sum_add_distrib]

theorem sum3_smul (s : ℝ) (f : Fin n → Fin n → Fin n → A) :
    sum3 (fun a b c => s • f a b c) = s • sum3 f := by
  simp only [sum3, Finset.smul_sum]

variable (P Q R : Fin n → A)
variable (hP : ∑ a, P a = 1) (hQ : ∑ b, Q b = 1) (hR : ∑ c, R c = 1)

include hP in
theorem short1 : sum3 (fun a _ _ => P a) = ((n:ℝ)^2) • (1:A) := by
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum, hP, smul_smul]
  congr 1
  ring

include hP hQ in
theorem short2 : sum3 (fun a b _ => P a * Q b) = (n:ℝ) • (1:A) := by
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum,
    ← Finset.mul_sum, hQ, mul_one, hP]

include hP hQ hR in
theorem short3 : sum3 (fun a b c => P a * Q b * R c) = (1:A) := by
  simp only [sum3, ← Finset.mul_sum, hR, mul_one, hQ, hP]

end MUMMoments
namespace MUMInterpolation
variable {A : Type*} [Ring A] [Algebra ℝ A]
noncomputable def cubic (N l : ℝ) : ℝ :=
  l^3 - 3*l^2 + (3*(N-1)/N)*l - (N-1)*(N-2)/N^2
noncomputable def quartic (N l : ℝ) : ℝ :=
  l^4 - 4*l^3 + (6*(N-1)/N)*l^2 - (4*(N-1)*(N-2)/N^2)*l +
    (N-1)*(N-2)*(N-3)/N^3
end MUMInterpolation
namespace SpectralPolynomialBounds
noncomputable section

def q3 (y t : ℝ) : ℝ := (t-1)^3 - 3*y^2*(t-1) - 2*y^4
def q4 (y t : ℝ) : ℝ :=
  (t-1)^4 - 6*y^2*(t-1)^2 - 8*y^4*(t-1) + 3*y^4 - 6*y^6

theorem test_negative (y : ℝ) (hy : 0 < y) : q4 y (1+9*y/4) < 0 := by
  have hp : 0 < y^4 * ((447:ℝ)/256 + 18*y + 6*y^2) := by positivity
  dsimp [q4]
  nlinarith

theorem four_positive (y : ℝ) (hy : 0 ≤ y) (hyb : y ≤ 3/4) : 0 < q4 y 4 := by
  have h2 : y^2 ≤ (9:ℝ)/16 := by nlinarith
  have h4 : y^4 ≤ (81:ℝ)/256 := by
    have h := mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 9/16+y^2 by positivity)
    nlinarith
  have h6 : y^6 ≤ (729:ℝ)/4096 := by
    have h := mul_nonneg (sub_nonneg.mpr h2) (sq_nonneg (y^2))
    nlinarith
  dsimp [q4]
  nlinarith

theorem largest_root_above_test (y lam : ℝ) (hy : 0 < y) (hyb : y ≤ 3/4)
    (hlam : IsGreatest {t : ℝ | q4 y t = 0} lam) : 1+9*y/4 < lam := by
  have hneg := test_negative y hy
  have hpos := four_positive y hy.le hyb
  have hcont : ContinuousOn (q4 y) (Set.Icc (1+9*y/4) 4) := by
    unfold q4
    fun_prop
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (show 1+9*y/4 ≤ (4:ℝ) by linarith)
    hcont (show (0:ℝ) ∈ Set.Icc (q4 y (1+9*y/4)) (q4 y 4) from ⟨hneg.le,hpos.le⟩)
  have hlt : 1+9*y/4 < t := by
    by_contra hn
    have he : t = 1+9*y/4 := le_antisymm (le_of_not_gt hn) ht.1
    rw [he] at hzero
    linarith
  exact hlt.trans_le (hlam.2 hzero)

theorem cubic_lower (y lam : ℝ) (hy : 0 < y) (hyb : y ≤ 3/4)
    (hlam : 1+9*y/4 < lam) : y^3*(297/64-2*y) < q3 y lam := by
  have hdiff : 0 < lam-1-9*y/4 := by linarith
  have hx : 0 < lam-1 := by linarith
  have hfactor : 0 < (lam-1)^2 + (lam-1)*(9*y/4) + (9*y/4)^2 - 3*y^2 := by
    have hxy : 0 ≤ (lam-1)*(9*y/4) := by positivity
    nlinarith [sq_nonneg (lam-1), sq_pos_of_pos hy]
  have h := mul_pos hdiff hfactor
  dsimp [q3]
  nlinarith

theorem coefficient_lower (y : ℝ) (hy : 0 ≤ y) (hyb : y ≤ 3/4) :
    (297/64:ℝ)^2 ≤ (1+9*y/4)*(297/64-2*y)^2 := by
  have hfactor : 0 ≤ (489753:ℝ)/16384 - (2417:ℝ)/64*y + 9*y^2 := by
    nlinarith [sq_nonneg y]
  have h := mul_nonneg hy hfactor
  nlinarith

theorem denominator_lower (y lam : ℝ) (hy : 0 < y) (hyb : y ≤ 3/4)
    (hlam : 1+9*y/4 < lam) :
    (297/64:ℝ)^2*y^6 < lam*(q3 y lam)^2 := by
  have hc := cubic_lower y lam hy hyb hlam
  have ha : 0 < (297/64:ℝ)-2*y := by linarith
  have hb : 0 < y^3*(297/64-2*y) := mul_pos (pow_pos hy 3) ha
  have hcpos : 0 < q3 y lam := hb.trans hc
  have hs : (y^3*(297/64-2*y))^2 < (q3 y lam)^2 := by nlinarith
  have ht := mul_lt_mul_of_pos_left hs (show 0 < 1+9*y/4 by positivity)
  have ht2 := mul_lt_mul_of_pos_right hlam (sq_pos_of_pos hcpos)
  have hcoeff := mul_le_mul_of_nonneg_right (coefficient_lower y hy.le hyb)
    (pow_nonneg hy.le 6)
  nlinarith

theorem kappa_upper (y lam : ℝ) (hy : 0 < y) (hyb : y ≤ 3/4)
    (hlam : IsGreatest {t : ℝ | q4 y t = 0} lam) :
    0 < y^6/(lam*(q3 y lam)^2) ∧
      y^6/(lam*(q3 y lam)^2) < (4096:ℝ)/88209 := by
  have h := denominator_lower y lam hy hyb (largest_root_above_test y lam hy hyb hlam)
  have hd : 0 < lam*(q3 y lam)^2 := lt_trans (by positivity) h
  constructor
  · exact div_pos (pow_pos hy 6) hd
  · apply (div_lt_iff₀ hd).2
    nlinarith

theorem positive_above_four (y t : ℝ) (hy : 0 ≤ y) (hyb : y ≤ 3/4)
    (ht : 4 ≤ t) : 0 < q4 y t := by
  have h2 : y^2 ≤ (9:ℝ)/16 := by nlinarith
  have h4 : y^4 ≤ (81:ℝ)/256 := by
    have h := mul_nonneg (sub_nonneg.mpr h2) (show 0 ≤ 9/16+y^2 by positivity)
    nlinarith
  have hz : 0 ≤ t-4 := by linarith
  have ha : 0 ≤ 54-6*y^2 := by nlinarith
  have hb : 0 ≤ 108-36*y^2-8*y^4 := by nlinarith
  have he : q4 y t-q4 y 4 =
      (t-4)^4 + 12*(t-4)^3 + (54-6*y^2)*(t-4)^2 +
        (108-36*y^2-8*y^4)*(t-4) := by unfold q4; ring
  have hle : q4 y 4 ≤ q4 y t := by
    apply sub_nonneg.mp
    rw [he]
    positivity
  exact (four_positive y hy hyb).trans_le hle

theorem exists_largest_root (y : ℝ) (hy : 0 < y) (hyb : y ≤ 3/4) :
    ∃ lam : ℝ, IsGreatest {t : ℝ | q4 y t = 0} lam := by
  have hneg := test_negative y hy
  have hpos := four_positive y hy.le hyb
  have hcont : Continuous (q4 y) := by unfold q4; fun_prop
  obtain ⟨t, ht, hzero⟩ := intermediate_value_Icc (show 1+9*y/4 ≤ (4:ℝ) by linarith)
    hcont.continuousOn
    (show (0:ℝ) ∈ Set.Icc (q4 y (1+9*y/4)) (q4 y 4) from ⟨hneg.le,hpos.le⟩)
  have hne : ({t : ℝ | q4 y t = 0} : Set ℝ).Nonempty := ⟨t,hzero⟩
  have hb : BddAbove {t : ℝ | q4 y t = 0} := by
    refine ⟨4, ?_⟩
    intro t ht
    by_contra hn
    have hp := positive_above_four y t hy.le hyb (le_of_lt (lt_of_not_ge hn))
    change q4 y t = 0 at ht
    linarith
  exact ⟨sSup {t : ℝ | q4 y t = 0},
    (isClosed_eq hcont continuous_const).isGreatest_csSup hne hb⟩

def originalCubic (N t : ℝ) : ℝ :=
  t^3-3*t^2+(3*(N-1)/N)*t-(N-1)*(N-2)/N^2
def originalQuartic (N t : ℝ) : ℝ :=
  t^4-4*t^3+(6*(N-1)/N)*t^2-(4*(N-1)*(N-2)/N^2)*t+
    (N-1)*(N-2)*(N-3)/N^3

theorem q3_eq_original (N y t : ℝ) (hN : N ≠ 0) (hy : y^2=1/N) :
    q3 y t = originalCubic N t := by
  have hy4 : y^4 = (1/N)^2 := by calc
    _ = (y^2)^2 := by ring
    _ = (1/N)^2 := by rw [hy]
  unfold q3 originalCubic
  rw [hy4,hy]
  field_simp
  <;> ring

theorem q4_eq_original (N y t : ℝ) (hN : N ≠ 0) (hy : y^2=1/N) :
    q4 y t = originalQuartic N t := by
  have hy4 : y^4 = (1/N)^2 := by calc
    _ = (y^2)^2 := by ring
    _ = (1/N)^2 := by rw [hy]
  have hy6 : y^6 = (1/N)^3 := by calc
    _ = (y^2)^3 := by ring
    _ = (1/N)^3 := by rw [hy]
  unfold q4 originalQuartic
  rw [hy6,hy4,hy]
  field_simp
  <;> ring

theorem inverse_sqrt_bounds (N : ℝ) (hN : 2 ≤ N) :
    0 < 1/Real.sqrt N ∧ 1/Real.sqrt N ≤ 3/4 ∧ (1/Real.sqrt N)^2=1/N := by
  have hpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hs : (Real.sqrt N)^2=N := Real.sq_sqrt (by linarith)
  refine ⟨div_pos (by norm_num) hpos, ?_, ?_⟩
  · apply (div_le_iff₀ hpos).2
    nlinarith [Real.sqrt_nonneg N]
  · rw [div_pow, one_pow, hs]

theorem original_exists_largest_root (N : ℝ) (hN : 2 ≤ N) :
    ∃ lam : ℝ, IsGreatest {t : ℝ | originalQuartic N t = 0} lam := by
  obtain ⟨hy,hyb,hysq⟩ := inverse_sqrt_bounds N hN
  have hNe : N ≠ 0 := by linarith
  have he := exists_largest_root (1/Real.sqrt N) hy hyb
  simpa only [q4_eq_original N _ _ hNe hysq] using he

theorem original_root_estimates (N lam : ℝ) (hN : 2 ≤ N)
    (hlam : IsGreatest {t : ℝ | originalQuartic N t=0} lam) :
    1+9/(4*Real.sqrt N) < lam ∧
    0 < 1/(N^3*lam*(originalCubic N lam)^2) ∧
      1/(N^3*lam*(originalCubic N lam)^2) < (4096:ℝ)/88209 := by
  obtain ⟨hy,hyb,hysq⟩ := inverse_sqrt_bounds N hN
  have hNe : N ≠ 0 := by linarith
  have hl : IsGreatest {t : ℝ | q4 (1/Real.sqrt N) t=0} lam := by
    simpa only [q4_eq_original N _ _ hNe hysq] using hlam
  have hlo := largest_root_above_test _ lam hy hyb hl
  have hk := kappa_upper _ lam hy hyb hl
  have hy6 : (1/Real.sqrt N)^6=(1/N)^3 := by calc
    _ = ((1/Real.sqrt N)^2)^3 := by ring
    _ = (1/N)^3 := by rw [hysq]
  rw [hy6, q3_eq_original N _ _ hNe hysq] at hk
  constructor
  · convert hlo using 1 <;> ring
  · convert hk using 1 <;> ring

end
end SpectralPolynomialBounds
namespace MUMSpectral
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {n D : ℕ}
local notation "M" => Mat D
noncomputable def tripleSum (P Q R : PVM n D) (abc : Fin n × (Fin n × Fin n)) : M :=
  P.proj abc.1+Q.proj abc.2.1+R.proj abc.2.2

noncomputable def cycleKappa (n : ℕ) (lam : ℝ) : ℝ :=
  1/((n:ℝ)^3*lam*(cubic n lam)^2)

noncomputable def tripleHarmonicMean (P Q R : PVM n D) (lam : ℝ) : M :=
  (matrixAverage fun abc => (lam • (1:M)-tripleSum P Q R abc)⁻¹)⁻¹

theorem tripleSum_nonneg (P Q R : PVM n D) (abc : Fin n × (Fin n × Fin n)) :
    0 ≤ tripleSum P Q R abc :=
  add_nonneg (add_nonneg (P.proj_nonneg abc.1) (Q.proj_nonneg abc.2.1))
    (R.proj_nonneg abc.2.2)

end MUMSpectral
namespace MUMShifted
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

noncomputable def average {ι : Type*} [Fintype ι] (A : ι → M) : M :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, A i

theorem inverse_smul (A : M) (hA : A.PosDef) (c : ℝ) (hc : c ≠ 0) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [smul_mul_assoc, mul_smul_comm, smul_smul,
    Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit),
    inv_mul_cancel₀ hc, one_smul]

theorem inverse_antitone {A B : M}
    (hA : A.PosDef) (hB : B.PosDef) (h : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  rw [Matrix.nonsing_inv_eq_ringInverse, Matrix.nonsing_inv_eq_ringInverse]
  exact CStarAlgebra.antitoneOn_ringInverse
    ⟨hA.posSemidef.nonneg, hA.isUnit⟩ ⟨hB.posSemidef.nonneg, hB.isUnit⟩ h

theorem average_posDef {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → M) (hA : ∀ i, (A i).PosDef) : (average A).PosDef := by
  apply Matrix.PosDef.smul
  · exact Matrix.posDef_sum Finset.univ_nonempty fun i _ => hA i
  · exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

theorem harmonic_le_smul {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → M) (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (B i).PosDef)
    (c : ℝ) (hc : 0 < c) (h : ∀ i, B i ≤ c • A i) :
    (average fun i => (B i)⁻¹)⁻¹ ≤ c • (average fun i => (A i)⁻¹)⁻¹ := by
  have hi (i : ι) : c⁻¹ • (A i)⁻¹ ≤ (B i)⁻¹ := by
    have hh := inverse_antitone (hB i) ((hA i).smul hc) (h i)
    rwa [inverse_smul (A i) (hA i) c hc.ne'] at hh
  have hmean : c⁻¹ • (average fun i => (A i)⁻¹) ≤ average fun i => (B i)⁻¹ := by
    unfold average
    rw [smul_comm c⁻¹, Finset.smul_sum]
    exact smul_le_smul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) (by positivity)
  have hap := average_posDef (fun i => (A i)⁻¹) (fun i => (hA i).inv)
  have hbp := average_posDef (fun i => (B i)⁻¹) (fun i => (hB i).inv)
  have hbound := inverse_antitone (hap.smul (inv_pos.mpr hc)) hbp hmean
  rw [inverse_smul _ hap c⁻¹ (inv_ne_zero hc.ne'), inv_inv] at hbound
  exact hbound

theorem add_scalar_le (A : M) (g delta : ℝ) (hg : 0 < g) (hd : 0 ≤ delta)
    (hA : g • (1:M) ≤ A) :
    A + delta • (1:M) ≤ (1+delta/g) • A := by
  have hs := smul_le_smul_of_nonneg_left hA (div_nonneg hd hg.le)
  have he : (delta/g)*g=delta := by field_simp
  rw [smul_smul, he] at hs
  calc
    _ ≤ A + (delta/g) • A := add_le_add le_rfl hs
    _ = _ := by rw [add_smul, one_smul]

theorem shifted_harmonic_comparison {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : ι → M) (g delta : ℝ) (hg : 0 < g) (hd : 0 ≤ delta)
    (hA : ∀ i, (A i).PosDef) (hB : ∀ i, (A i + delta • (1:M)).PosDef)
    (hgap : ∀ i, g • (1:M) ≤ A i) :
    (average fun i => (A i + delta • (1:M))⁻¹)⁻¹ ≤
      (1+delta/g) • (average fun i => (A i)⁻¹)⁻¹ :=
  harmonic_le_smul A (fun i => A i+delta • (1:M)) hA hB (1+delta/g)
    (by positivity) (fun i => add_scalar_le (A i) g delta hg hd (hgap i))
end MUMShifted
end
section
namespace MUMSpectral
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {n D : ℕ}
local notation "M" => Mat D

theorem selected_gt_of_harmonic_trace_lt
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (hn : 0<n) (hD : 0<D) (S : ι → M) (T : PVM n D) (lam g : ℝ)
    (hg : 0<g) (hS : ∀ i, 0≤S i)
    (hgap : ∀ i, g • (1:M) ≤ lam • 1-S i)
    (htrace : matTrace ((matrixAverage fun i => (lam • 1-S i)⁻¹)⁻¹) < (D:ℝ)) :
    ∃ i j, lam < ‖S i+T.proj j‖ := by
  let A : ι → M := fun i => lam • 1-S i
  let h : ℝ := matTrace ((matrixAverage fun i => (A i)⁻¹)⁻¹)
  have hsmall : h<(D:ℝ) := htrace
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  let delta : ℝ := g*((D:ℝ)-h)/(2*(D:ℝ))
  have hd : 0<delta := div_pos (mul_pos hg (sub_pos.mpr hsmall)) (by positivity)
  have hid : delta/g*(D:ℝ)=((D:ℝ)-h)/2 := by
    dsimp [delta]
    field_simp
  have hA : ∀ i, (A i).PosDef := fun i => posDef_of_scalar_lower hg (hgap i)
  have hB : ∀ i, (A i+delta • (1:M)).PosDef := fun i =>
    (hA i).add_posSemidef ((Matrix.PosDef.one.smul hd).posSemidef)
  have hcomp := MUMShifted.shifted_harmonic_comparison A g delta hg hd.le hA hB hgap
  have hct := matrix_trace_mono hcomp
  have hshift (i : ι) : A i+delta • (1:M)=(lam+delta) • 1-S i := by dsimp [A]; module
  simp_rw [hshift] at hct
  change matTrace ((matrixAverage fun i => ((lam+delta) • 1-S i)⁻¹)⁻¹) ≤
    matTrace ((1+delta/g) • ((matrixAverage fun i => (A i)⁻¹)⁻¹)) at hct
  have hu : matTrace ((matrixAverage fun i => ((lam+delta) • 1-S i)⁻¹)⁻¹)<(D:ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hsmall.le (div_nonneg hd.le hg.le)
    simp only [matTrace, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hct
    change _ ≤ (1+delta/g)*h at hct
    unfold matTrace
    nlinarith
  obtain ⟨i,j,hij⟩ := selected_norm_of_harmonic_trace hn hD S T (lam+delta) hS (fun _ => hu.le)
  exact ⟨i,j,lt_of_lt_of_le (by linarith) hij⟩

theorem selfAdjoint_eq_zero_of_trace_square (A : M) (hA : IsSelfAdjoint A)
    (ht : matTrace (A^2)=0) : A=0 := by
  have hp := Matrix.nonneg_iff_posSemidef.mp hA.sq_nonneg
  have hi := (Complex.nonneg_iff.mp hp.trace_nonneg).2
  have hz : Matrix.trace (A^2)=0 := Complex.ext ht hi.symm
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  change Matrix.trace (star A*A)=0
  rw [hA.star_eq, ← pow_two]
  exact hz

theorem defect_eq_zero_of_trace_defectSquares (P Q R : PVM n D)
    (ht : matTrace (defectSquares P Q R)=0) : ∀ a b c, defect P Q R a b c=0 := by
  have hnon (a b c : Fin n) : 0≤matTrace ((defect P Q R a b c)^2) := by
    have h := matrix_trace_mono (defect_selfAdjoint P Q R a b c).sq_nonneg
    simpa only [matTrace, Matrix.trace_zero, Complex.zero_re] using h
  have hs : ∑ a, ∑ b, ∑ c, matTrace ((defect P Q R a b c)^2)=0 := by
    simpa only [matTrace, defectSquares, Matrix.trace_sum, Complex.re_sum] using ht
  intro a b c
  have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => Finset.sum_nonneg (fun c _ => hnon a b c)))).mp hs a (Finset.mem_univ _)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ =>
    Finset.sum_nonneg (fun c _ => hnon a b c))).mp ha b (Finset.mem_univ _)
  have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hnon a b c)).mp hb c (Finset.mem_univ _)
  exact selfAdjoint_eq_zero_of_trace_square _ (defect_selfAdjoint P Q R a b c) hc

end MUMSpectral

end
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section

def pairDefect {n D : ℕ} (P Q : PVM n D) (a b : Fin n) : Mat D :=
  P.proj a * Q.proj b * P.proj a - (n : ℝ)⁻¹ • P.proj a

def pairSigma {n D : ℕ} (P Q : PVM n D) : ℝ :=
  ∑ a, ∑ b, matTrace ((pairDefect P Q a b)^2)

def pairKappa {n D : ℕ} (P Q : PVM n D) : ℝ :=
  ∑ a, ∑ b, matTrace ((pairDefect P Q a b)^3)

def anchorVariance {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  ∑ a, ∑ b, ∑ c, matTrace ((defect P Q R a b c)^2)

def anchorRho {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  ∑ a, ∑ b, ∑ c, matTrace (pairDefect Q P b a * pairDefect R P c a)

def anchorXi {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  ∑ a, ∑ b, ∑ c,
    matTrace (pairDefect P R a c * defect P Q R a b c * pairDefect P Q a b)

def totalSigma {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  pairSigma P Q + pairSigma Q R + pairSigma R P
def totalKappa {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  pairKappa P Q + pairKappa Q R + pairKappa R P
def totalVariance {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  anchorVariance P Q R + anchorVariance Q R P + anchorVariance R P Q
def totalRho {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  anchorRho P Q R + anchorRho Q R P + anchorRho R P Q
def totalXi {n D : ℕ} (P Q R : PVM n D) : ℝ :=
  anchorXi P Q R + anchorXi Q R P + anchorXi R P Q

def moment {n D : ℕ} (P Q R : PVM n D) (k : ℕ) : ℝ :=
  (∑ a, ∑ b, ∑ c, matTrace ((P.proj a + Q.proj b + R.proj c)^k)) / (n : ℝ)^3

def IsThreeUM {n D : ℕ} (P Q R : PVM n D) : Prop :=
  Unbiased P Q ∧ Unbiased Q R ∧ Unbiased R P ∧
  ∀ a b c, defect P Q R a b c = 0 ∧
    defect Q R P b c a = 0 ∧ defect R P Q c a b = 0

def ArbitraryRankFourBound : Prop :=
  ∀ (n D : ℕ), 2 ≤ n → 0 < D →
  ∀ (P Q R T : PVM n D) (lam : ℝ), LargestRoot n lam →
    ∃ a b c e : Fin n, lam ≤ ‖selectedSum P Q R T a b c e‖

def ArbitraryRankFourRigidity : Prop :=
  ∀ (n D : ℕ), 2 ≤ n → 0 < D →
  ∀ (P Q R T : PVM n D) (lam : ℝ), LargestRoot n lam →
    (∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) →
    IsThreeUM P Q R ∧ IsThreeUM P Q T ∧ IsThreeUM P R T ∧ IsThreeUM Q R T

end
end FourMeas
end

section
namespace FourMeasScalars
open MUMSpectral SpectralPolynomialBounds
noncomputable section

theorem root_bounds {n : ℕ} (hn : 2 ≤ n) (lam : ℝ)
    (hlam : LargestRoot n lam) :
    0 < lam ∧ 0 < MUMSpectral.cubic n lam ∧
      (81 : ℝ)/16 < (n : ℝ)*(lam-1)^2 := by
  have hN : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hNp : (0 : ℝ) < n := by linarith
  have hNe : (n : ℝ) ≠ 0 := ne_of_gt hNp
  obtain ⟨hy, hyb, hysq⟩ := inverse_sqrt_bounds (n : ℝ) hN
  have hr : IsGreatest {t : ℝ | originalQuartic (n : ℝ) t = 0} lam := hlam
  have hq : IsGreatest {t : ℝ | q4 (1/Real.sqrt (n : ℝ)) t = 0} lam := by
    simpa only [q4_eq_original (n : ℝ) _ _ hNe hysq] using hr
  have hlo := largest_root_above_test _ lam hy hyb hq
  have hc := cubic_lower _ lam hy hyb hlo
  have hcoef : 0 < (297/64 : ℝ)-2*(1/Real.sqrt (n : ℝ)) := by linarith
  have hp : 0 < (1/Real.sqrt (n : ℝ))^3*((297/64 : ℝ)-2*(1/Real.sqrt (n : ℝ))) :=
    mul_pos (pow_pos hy 3) hcoef
  rw [q3_eq_original (n : ℝ) _ _ hNe hysq] at hc
  have hcpos : 0 < MUMSpectral.cubic n lam := lt_trans hp hc
  have hx : 0 < lam-1 := by linarith
  have hs : (81 : ℝ)/16*(1/Real.sqrt (n : ℝ))^2 < (lam-1)^2 := by
    nlinarith [mul_pos (show 0 < lam-1-9*(1/Real.sqrt (n : ℝ))/4 by linarith)
      (show 0 < lam-1+9*(1/Real.sqrt (n : ℝ))/4 by positivity)]
  have hmul := mul_lt_mul_of_pos_left hs hNp
  have hunit : (n : ℝ)*(1/Real.sqrt (n : ℝ))^2 = 1 := by
    rw [hysq]
    field_simp
  refine ⟨by linarith, hcpos, ?_⟩
  nlinarith

theorem omega_positive {n : ℕ} (hn : 2 ≤ n) (lam : ℝ)
    (hlam : LargestRoot n lam) : 0 < lam * MUMSpectral.cubic n lam :=
  mul_pos (root_bounds hn lam hlam).1 (root_bounds hn lam hlam).2.1

def coeff1 (N l : ℝ) : ℝ := -((N-1)*(N-2)/N^2)*originalCubic N l
def coeff2 (N l : ℝ) : ℝ := (3*(N-1)/N)*originalCubic N l -
  ((N-1)*(N-2)/N^2)*(l^2-3*l+3*(N-1)/N)
def coeff3 (N l : ℝ) : ℝ := -3*originalCubic N l +
  (3*(N-1)/N)*(l^2-3*l+3*(N-1)/N) - ((N-1)*(N-2)/N^2)*(l-3)
def coeff4 (N l : ℝ) : ℝ := l^3-6*l^2+(9+6*(N-1)/N)*l-
  18*(N-1)/N-2*(N-1)*(N-2)/N^2
def coeff5 (N l : ℝ) : ℝ := (l-3)^2+6*(N-1)/N
def coeff6 (l : ℝ) : ℝ := l-6

theorem omega_G_coefficients (N l t : ℝ) :
    (t*originalCubic N t)*
      (t^3+(l-3)*t^2+(l^2-3*l+3*(N-1)/N)*t+originalCubic N l) =
    coeff1 N l*t + coeff2 N l*t^2 + coeff3 N l*t^3 +
    coeff4 N l*t^4 + coeff5 N l*t^5 + coeff6 l*t^6 + t^7 := by
  unfold coeff1 coeff2 coeff3 coeff4 coeff5 coeff6 originalCubic
  ring

theorem ideal_moment_cancellation (N l : ℝ) (hN : N ≠ 0) :
    coeff1 N l*(3/N) + coeff2 N l*(3/N+6/N^2) +
    coeff3 N l*(3/N+18/N^2+6/N^3) +
    coeff4 N l*(3/N+36/N^2+42/N^3) +
    coeff5 N l*(3/N+60/N^2+150/N^3+30/N^4) +
    coeff6 l*(3/N+90/N^2+390/N^3+234/N^4+12/N^5) +
    (3/N+126/N^2+840/N^3+1008/N^4+210/N^5) = 0 := by
  unfold coeff1 coeff2 coeff3 coeff4 coeff5 coeff6 originalCubic
  field_simp
  ring

theorem weighted_defect_expansion (N x s k V r z : ℝ) (hN : N ≠ 0) :
    coeff4 N (x+1)*(2*N*s) + coeff5 N (x+1)*((10*N+10)*s) +
    coeff6 (x+1)*((30*N+78)*s+2*N*k+V+4*r) +
    ((70*N+336+98/N)*s+(14*N+14)*k+7*V+28*r+14*z) =
    (2*N*x^3+(4*N+10)*x^2+(2*N+26)*x+22+30/N)*s +
    (2*N*x+4*N+14)*k + (x+2)*(V+4*r)+14*z := by
  unfold coeff4 coeff5 coeff6
  field_simp
  ring

end
end FourMeasScalars
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
private theorem aux3_idem_tail {D : ℕ} (a b : Mat D) (h : a*a=a) : a*(a*b)=a*b := by
  rw [← mul_assoc,h]
theorem sum3_sandwich {n D : ℕ} (P Q : PVM n D) :
    sum3 (fun a b (_ : Fin n) => P.proj a * Q.proj b * P.proj a) =
      (n : ℝ) • (1 : Mat D) := by
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Finset.smul_sum, ← Finset.sum_mul,
    ← Finset.mul_sum, Q.complete, mul_one, fun a => (P.isProj a).isIdempotentElem.eq,
    P.complete]

theorem matrix_power_1 {D : ℕ} (p q r : Mat D) (hp : p*p=p) (hq : q*q=q) (hr : r*r=r) : (p+q+r)^1 = (1 : ℝ) • (p) + (1 : ℝ) • (q) + (1 : ℝ) • (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux3_idem_tail p _ hp, aux3_idem_tail q _ hq, aux3_idem_tail r _ hr]
  all_goals module
theorem matrix_power_2 {D : ℕ} (p q r : Mat D) (hp : p*p=p) (hq : q*q=q) (hr : r*r=r) : (p+q+r)^2 = (1 : ℝ) • (p) + (1 : ℝ) • (p*q) + (1 : ℝ) • (p*r) + (1 : ℝ) • (q) + (1 : ℝ) • (q*p) + (1 : ℝ) • (q*r) + (1 : ℝ) • (r) + (1 : ℝ) • (r*p) + (1 : ℝ) • (r*q) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux3_idem_tail p _ hp, aux3_idem_tail q _ hq, aux3_idem_tail r _ hr]
  all_goals module
theorem matrix_power_3 {D : ℕ} (p q r : Mat D) (hp : p*p=p) (hq : q*q=q) (hr : r*r=r) : (p+q+r)^3 = (1 : ℝ) • (p) + (2 : ℝ) • (p*q) + (1 : ℝ) • (p*q*p) + (1 : ℝ) • (p*q*r) + (2 : ℝ) • (p*r) + (1 : ℝ) • (p*r*p) + (1 : ℝ) • (p*r*q) + (1 : ℝ) • (q) + (2 : ℝ) • (q*p) + (1 : ℝ) • (q*p*q) + (1 : ℝ) • (q*p*r) + (2 : ℝ) • (q*r) + (1 : ℝ) • (q*r*p) + (1 : ℝ) • (q*r*q) + (1 : ℝ) • (r) + (2 : ℝ) • (r*p) + (1 : ℝ) • (r*p*q) + (1 : ℝ) • (r*p*r) + (2 : ℝ) • (r*q) + (1 : ℝ) • (r*q*p) + (1 : ℝ) • (r*q*r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux3_idem_tail p _ hp, aux3_idem_tail q _ hq, aux3_idem_tail r _ hr]
  all_goals module
theorem raw_low_moments {n D : ℕ} (P Q R : PVM n D) :
  sum3 (fun a b c => (P.proj a+Q.proj b+R.proj c)^1) = (3*(n:ℝ)^2) • (1 : Mat D) ∧
  sum3 (fun a b c => (P.proj a+Q.proj b+R.proj c)^2) = (3*(n:ℝ)^2+6*n) • (1 : Mat D) ∧
  sum3 (fun a b c => (P.proj a+Q.proj b+R.proj c)^3) = (3*(n:ℝ)^2+18*n+6) • (1 : Mat D) := by
  have w_p : sum3 (fun a b c => P.proj a) = ((n:ℝ)^2) • (1 : Mat D) := by
    have hw := short1 P.proj P.complete
    simpa only [one_smul] using hw
  have w_q : sum3 (fun a b c => Q.proj b) = ((n:ℝ)^2) • (1 : Mat D) := by
    have hw := short1 Q.proj Q.complete
    rw [← sum3_bac (fun a b c => Q.proj a)] at hw
    simpa only [one_smul] using hw
  have w_r : sum3 (fun a b c => R.proj c) = ((n:ℝ)^2) • (1 : Mat D) := by
    have hw := short1 R.proj R.complete
    rw [← sum3_cab (fun a b c => R.proj a)] at hw
    simpa only [one_smul] using hw
  have w_pq : sum3 (fun a b c => P.proj a * Q.proj b) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 P.proj Q.proj P.complete Q.complete
    simpa only [one_smul] using hw
  have w_pr : sum3 (fun a b c => P.proj a * R.proj c) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 P.proj R.proj P.complete R.complete
    rw [← sum3_acb (fun a b c => P.proj a * R.proj b)] at hw
    simpa only [one_smul] using hw
  have w_qp : sum3 (fun a b c => Q.proj b * P.proj a) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 Q.proj P.proj Q.complete P.complete
    rw [← sum3_bac (fun a b c => Q.proj a * P.proj b)] at hw
    simpa only [one_smul] using hw
  have w_qr : sum3 (fun a b c => Q.proj b * R.proj c) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 Q.proj R.proj Q.complete R.complete
    rw [← sum3_bca (fun a b c => Q.proj a * R.proj b)] at hw
    simpa only [one_smul] using hw
  have w_rp : sum3 (fun a b c => R.proj c * P.proj a) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 R.proj P.proj R.complete P.complete
    rw [← sum3_cab (fun a b c => R.proj a * P.proj b)] at hw
    simpa only [one_smul] using hw
  have w_rq : sum3 (fun a b c => R.proj c * Q.proj b) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := short2 R.proj Q.proj R.complete Q.complete
    rw [← sum3_cba (fun a b c => R.proj a * Q.proj b)] at hw
    simpa only [one_smul] using hw
  have w_pqp : sum3 (fun a b c => P.proj a * Q.proj b * P.proj a) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich P Q
    simpa only [one_smul] using hw
  have w_pqr : sum3 (fun a b c => P.proj a * Q.proj b * R.proj c) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 P.proj Q.proj R.proj P.complete Q.complete R.complete
    simpa only [one_smul] using hw
  have w_prp : sum3 (fun a b c => P.proj a * R.proj c * P.proj a) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich P R
    rw [← sum3_acb (fun a b c => P.proj a * R.proj b * P.proj a)] at hw
    simpa only [one_smul] using hw
  have w_prq : sum3 (fun a b c => P.proj a * R.proj c * Q.proj b) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 P.proj R.proj Q.proj P.complete R.complete Q.complete
    rw [← sum3_acb (fun a b c => P.proj a * R.proj b * Q.proj c)] at hw
    simpa only [one_smul] using hw
  have w_qpq : sum3 (fun a b c => Q.proj b * P.proj a * Q.proj b) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich Q P
    rw [← sum3_bac (fun a b c => Q.proj a * P.proj b * Q.proj a)] at hw
    simpa only [one_smul] using hw
  have w_qpr : sum3 (fun a b c => Q.proj b * P.proj a * R.proj c) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 Q.proj P.proj R.proj Q.complete P.complete R.complete
    rw [← sum3_bac (fun a b c => Q.proj a * P.proj b * R.proj c)] at hw
    simpa only [one_smul] using hw
  have w_qrp : sum3 (fun a b c => Q.proj b * R.proj c * P.proj a) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 Q.proj R.proj P.proj Q.complete R.complete P.complete
    rw [← sum3_bca (fun a b c => Q.proj a * R.proj b * P.proj c)] at hw
    simpa only [one_smul] using hw
  have w_qrq : sum3 (fun a b c => Q.proj b * R.proj c * Q.proj b) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich Q R
    rw [← sum3_bca (fun a b c => Q.proj a * R.proj b * Q.proj a)] at hw
    simpa only [one_smul] using hw
  have w_rpq : sum3 (fun a b c => R.proj c * P.proj a * Q.proj b) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 R.proj P.proj Q.proj R.complete P.complete Q.complete
    rw [← sum3_cab (fun a b c => R.proj a * P.proj b * Q.proj c)] at hw
    simpa only [one_smul] using hw
  have w_rpr : sum3 (fun a b c => R.proj c * P.proj a * R.proj c) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich R P
    rw [← sum3_cab (fun a b c => R.proj a * P.proj b * R.proj a)] at hw
    simpa only [one_smul] using hw
  have w_rqp : sum3 (fun a b c => R.proj c * Q.proj b * P.proj a) = ((1:ℝ)) • (1 : Mat D) := by
    have hw := short3 R.proj Q.proj P.proj R.complete Q.complete P.complete
    rw [← sum3_cba (fun a b c => R.proj a * Q.proj b * P.proj c)] at hw
    simpa only [one_smul] using hw
  have w_rqr : sum3 (fun a b c => R.proj c * Q.proj b * R.proj c) = ((n:ℝ)) • (1 : Mat D) := by
    have hw := sum3_sandwich R Q
    rw [← sum3_cba (fun a b c => R.proj a * Q.proj b * R.proj a)] at hw
    simpa only [one_smul] using hw
  refine ⟨?_,?_,?_⟩
  · have heq (a b c : Fin n) := matrix_power_1 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    simp_rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r]
    module
  · have heq (a b c : Fin n) := matrix_power_2 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    simp_rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq]
    module
  · have heq (a b c : Fin n) := matrix_power_3 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    simp_rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqp, w_pqr, w_prp, w_prq, w_qpq, w_qpr, w_qrp, w_qrq, w_rpq, w_rpr, w_rqp, w_rqr]
    module
end FourMeas
end

section
open scoped BigOperators Matrix ComplexConjugate MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix MUMSpectral

namespace Harmonic

variable {D : ℕ} {ι : Type*} [Fintype ι]
local notation "M" => MUMSpectral.Mat D

theorem average_add (A B : ι → M) :
    matrixAverage (fun i => A i + B i) = matrixAverage A + matrixAverage B := by
  simp [matrixAverage, Finset.sum_add_distrib, smul_add]

theorem average_sub (A B : ι → M) :
    matrixAverage (fun i => A i - B i) = matrixAverage A - matrixAverage B := by
  simp [matrixAverage, Finset.sum_sub_distrib, smul_sub]

theorem average_smul (c : ℝ) (A : ι → M) :
    matrixAverage (fun i => c • A i) = c • matrixAverage A := by
  simp only [matrixAverage, ← Finset.smul_sum]
  exact smul_comm _ _ _

theorem average_mul_left (B : M) (A : ι → M) :
    matrixAverage (fun i => B * A i) = B * matrixAverage A := by
  simp [matrixAverage, ← Finset.mul_sum, mul_smul_comm]

theorem average_mul_right (A : ι → M) (B : M) :
    matrixAverage (fun i => A i * B) = matrixAverage A * B := by
  simp [matrixAverage, ← Finset.sum_mul, smul_mul_assoc]

theorem average_adjoint (A : ι → M) :
    matrixAverage (fun i => (A i)ᴴ) = (matrixAverage A)ᴴ := by
  simp [matrixAverage, Matrix.conjTranspose_sum]

theorem complete_square (A X H Y : M) (hAX : A * X = H) (hXA : Xᴴ * A = H) :
    (Y-X)ᴴ * A * (Y-X) = Yᴴ*A*Y - Yᴴ*H - H*Y + H*X := by
  calc
    _ = Yᴴ*A*Y - Yᴴ*(A*X) - (Xᴴ*A)*Y + (Xᴴ*A)*X := by
      rw [Matrix.conjTranspose_sub]
      noncomm_ring
    _ = _ := by rw [hAX, hXA]

theorem variational_matrix_bound [Nonempty ι]
    (A Y : ι → M) (hA : ∀ i, (A i).PosDef)
    (hY : matrixAverage Y = 1) :
    (matrixAverage fun i => (A i)⁻¹)⁻¹ ≤ matrixAverage (fun i => (Y i)ᴴ * A i * Y i) := by
  let B : M := matrixAverage fun i => (A i)⁻¹
  let H : M := B⁻¹
  let X : ι → M := fun i => (A i)⁻¹ * H
  have hB : B.PosDef := matrixAverage_posDef _ (fun i => (hA i).inv)
  have hH : Hᴴ = H := hB.inv.isHermitian.eq
  have hBH : B*H=1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det _).mp hB.isUnit)
  have hAX (i : ι) : A i * X i = H := by
    dsimp [X]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hA i).isUnit), one_mul]
  have hXA (i : ι) : (X i)ᴴ * A i = H := by
    dsimp [X]
    rw [Matrix.conjTranspose_mul, hH, (hA i).inv.isHermitian.eq,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (hA i).isUnit), mul_one]
  have hX : matrixAverage X = 1 := by
    change matrixAverage (fun i => (A i)⁻¹ * H) = 1
    rw [average_mul_right]
    exact hBH
  have hp : 0 ≤ matrixAverage (fun i => (Y i-X i)ᴴ * A i * (Y i-X i)) := by
    have hm := matrixAverage_mono (fun i => ((hA i).posSemidef.conjTranspose_mul_mul_same (Y i-X i)).nonneg)
    simpa only [matrixAverage_const] using hm
  have heq : matrixAverage (fun i => (Y i-X i)ᴴ * A i * (Y i-X i)) =
      matrixAverage (fun i => (Y i)ᴴ * A i * Y i) - H := by
    simp_rw [complete_square (A _) (X _) H (Y _) (hAX _) (hXA _)]
    rw [average_add, average_sub, average_sub, average_mul_right, average_adjoint,
      average_mul_left, average_mul_left, hY, hX]
    simp
  rw [heq] at hp
  exact sub_nonneg.mp hp

theorem variational_trace_bound [Nonempty ι]
    (A Y : ι → M) (hA : ∀ i, (A i).PosDef)
    (hY : matrixAverage Y = 1) :
    matTrace ((matrixAverage fun i => (A i)⁻¹)⁻¹) ≤
      matTrace (matrixAverage (fun i => (Y i)ᴴ * A i * Y i)) :=
  matrix_trace_mono (variational_matrix_bound A Y hA hY)

theorem four_pvm_of_harmonic_bound {n D : ℕ}
    (P Q R T : PVM n D) (hn : 2 ≤ n) (hD : 0 < D) (lam : ℝ)
    (htrace : (∀ abc, (lam • (1 : MUMSpectral.Mat D)-tripleSum P Q R abc).PosDef) →
      matTrace (tripleHarmonicMean P Q R lam) ≤ (D : ℝ)) :
    ∃ a b c d : Fin n, lam ≤ ‖selectedSum P Q R T a b c d‖ := by
  have hnpos : 0 < n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  obtain ⟨⟨a,b,c⟩,d,h⟩ := selected_norm_of_harmonic_trace hnpos hD
    (tripleSum P Q R) T lam (tripleSum_nonneg P Q R) htrace
  exact ⟨a,b,c,d,h⟩

noncomputable def omega (n : ℕ) (S : M) : M :=
  S^4 - (3:ℝ) • S^3 + (3*((n:ℝ)-1)/(n:ℝ)) • S^2 -
    (((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2) • S

noncomputable def cubicTest (n : ℕ) (lam : ℝ) (S : M) : M :=
  S^3 + (lam-3) • S^2 + (lam^2-3*lam+3*((n:ℝ)-1)/(n:ℝ)) • S +
    MUMSpectral.cubic n lam • (1:M)

theorem cubicTest_identity (n : ℕ) (lam : ℝ) (S : M) :
    (lam • (1:M)-S)*cubicTest n lam S =
      (lam*MUMSpectral.cubic n lam) • (1:M)-omega n S := by
  simp only [cubicTest, omega, MUMSpectral.cubic, pow_succ, pow_zero, mul_one,
    one_mul, mul_add, add_mul, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_assoc]
  module

theorem cubicTest_selfAdjoint (n : ℕ) (lam : ℝ) (S : M) (hS : IsSelfAdjoint S) :
    IsSelfAdjoint (cubicTest n lam S) := by
  change star (cubicTest n lam S) = cubicTest n lam S
  simp only [cubicTest, star_add, star_smul, star_pow, star_trivial, star_one, hS.star_eq]

theorem cubicTest_commute (n : ℕ) (lam : ℝ) (S : M) :
    Commute (cubicTest n lam S) S := by
  change cubicTest n lam S*S=S*cubicTest n lam S
  simp only [cubicTest, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  noncomm_ring

theorem cubic_average_scalar (N l : ℝ) (hN : N ≠ 0) :
    3*(N^2+6*N+2)/N^3 + (l-3)*(3*(N+2)/N^2) +
      (l^2-3*l+3*(N-1)/N)*(3/N) + MUMInterpolation.cubic N l =
      l*MUMInterpolation.cubic N l-MUMInterpolation.quartic N l := by
  unfold MUMInterpolation.cubic MUMInterpolation.quartic
  field_simp
  <;> ring

theorem average_triple {n : ℕ} (F : Fin n → Fin n → Fin n → M) :
    matrixAverage (fun abc : Fin n × Fin n × Fin n => F abc.1 abc.2.1 abc.2.2) =
      ((n:ℝ)^3)⁻¹ • MUMMoments.sum3 F := by
  simp [matrixAverage, Fintype.sum_prod_type, MUMMoments.sum3, pow_succ, mul_assoc]

theorem normalized_low_moments {n : ℕ} (P Q R : PVM n D) (hn : n ≠ 0) :
    matrixAverage (tripleSum P Q R) = (3/(n:ℝ)) • (1:M) ∧
    matrixAverage (fun abc => (tripleSum P Q R abc)^2) =
      (3*((n:ℝ)+2)/(n:ℝ)^2) • (1:M) ∧
    matrixAverage (fun abc => (tripleSum P Q R abc)^3) =
      (3*((n:ℝ)^2+6*n+2)/(n:ℝ)^3) • (1:M) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨h1,h2,h3⟩ := FourMeas.raw_low_moments P Q R
  refine ⟨?_,?_,?_⟩
  · change matrixAverage (fun abc : Fin n × Fin n × Fin n => P.proj abc.1+Q.proj abc.2.1+R.proj abc.2.2) = _
    simp only [pow_one] at h1
    rw [average_triple (fun a b c => P.proj a+Q.proj b+R.proj c), h1, smul_smul]
    congr 1
    field_simp [hnR]
  · change matrixAverage (fun abc : Fin n × Fin n × Fin n => (P.proj abc.1+Q.proj abc.2.1+R.proj abc.2.2)^2) = _
    rw [average_triple (fun a b c => (P.proj a+Q.proj b+R.proj c)^2), h2, smul_smul]
    congr 1
    field_simp [hnR]
    <;> ring
  · change matrixAverage (fun abc : Fin n × Fin n × Fin n => (P.proj abc.1+Q.proj abc.2.1+R.proj abc.2.2)^3) = _
    rw [average_triple (fun a b c => (P.proj a+Q.proj b+R.proj c)^3), h3, smul_smul]
    congr 1
    field_simp [hnR]
    <;> ring

theorem cubicTest_average {n : ℕ} (P Q R : PVM n D) (hn : n ≠ 0)
    (lam : ℝ) (hroot : MUMSpectral.quartic n lam = 0) :
    matrixAverage (fun abc => cubicTest n lam (tripleSum P Q R abc)) =
      (lam*MUMSpectral.cubic n lam) • (1:M) := by
  letI : NeZero n := ⟨hn⟩
  obtain ⟨h1,h2,h3⟩ := normalized_low_moments P Q R hn
  simp only [cubicTest, average_add, average_smul, matrixAverage_const, h1,h2,h3,
    smul_smul, ← add_smul]
  congr 1
  have h := cubic_average_scalar (n:ℝ) lam (by exact_mod_cast hn)
  change _ = lam*MUMSpectral.cubic n lam-MUMSpectral.quartic n lam at h
  simpa only [hroot, sub_zero, MUMInterpolation.cubic, MUMSpectral.cubic] using h

theorem cubicTest_quadratic {n : ℕ} (lam : ℝ) (S : M) (hS : IsSelfAdjoint S) :
    (cubicTest n lam S)ᴴ * (lam • (1:M)-S) * cubicTest n lam S =
      (lam*MUMSpectral.cubic n lam) • cubicTest n lam S - omega n S*cubicTest n lam S := by
  have hself : (cubicTest n lam S)ᴴ = cubicTest n lam S :=
    (cubicTest_selfAdjoint n lam S hS).star_eq
  have hc : cubicTest n lam S * (lam • (1:M)-S) =
      (lam • (1:M)-S)*cubicTest n lam S := by
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
    rw [(cubicTest_commute n lam S).eq]
  rw [hself, hc, cubicTest_identity, sub_mul, smul_mul_assoc, one_mul]

noncomputable def normalizedTest (n : ℕ) (lam : ℝ) (S : M) : M :=
  (lam*MUMSpectral.cubic n lam)⁻¹ • cubicTest n lam S

theorem normalizedTest_average {n : ℕ} (P Q R : PVM n D) (hn : n ≠ 0)
    (lam : ℝ) (hroot : MUMSpectral.quartic n lam = 0)
    (hw : lam*MUMSpectral.cubic n lam ≠ 0) :
    matrixAverage (fun abc => normalizedTest n lam (tripleSum P Q R abc)) = 1 := by
  simp only [normalizedTest]
  rw [average_smul, cubicTest_average P Q R hn lam hroot,
    smul_smul, inv_mul_cancel₀ hw, one_smul]

theorem normalizedTest_quadratic {n : ℕ} (lam : ℝ) (S : M) (hS : IsSelfAdjoint S)
    (hw : lam*MUMSpectral.cubic n lam ≠ 0) :
    (normalizedTest n lam S)ᴴ * (lam • (1:M)-S) * normalizedTest n lam S =
      normalizedTest n lam S - ((lam*MUMSpectral.cubic n lam)^2)⁻¹ •
        (omega n S*cubicTest n lam S) := by
  simp only [normalizedTest, Matrix.conjTranspose_smul, star_trivial,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [cubicTest_quadratic lam S hS, smul_sub, smul_smul]
  congr 1
  · congr 1
    field_simp
  · congr 1
    simp [pow_two, _root_.mul_inv_rev]

theorem harmonic_trace_deficit {n : ℕ} (P Q R : PVM n D) (hn : n ≠ 0)
    (lam : ℝ) (hroot : MUMSpectral.quartic n lam = 0)
    (hw : lam*MUMSpectral.cubic n lam ≠ 0)
    (hres : ∀ abc, (lam • (1:M)-tripleSum P Q R abc).PosDef) :
    matTrace (tripleHarmonicMean P Q R lam) ≤ (D:ℝ) -
      matTrace (matrixAverage (fun abc => omega n (tripleSum P Q R abc) *
        cubicTest n lam (tripleSum P Q R abc))) / (lam*MUMSpectral.cubic n lam)^2 := by
  letI : NeZero n := ⟨hn⟩
  have hy := normalizedTest_average P Q R hn lam hroot hw
  have h := variational_trace_bound (fun abc => lam • (1:M)-tripleSum P Q R abc)
    (fun abc => normalizedTest n lam (tripleSum P Q R abc)) hres hy
  simp_rw [normalizedTest_quadratic lam _ (tripleSum_nonneg P Q R _).isSelfAdjoint hw] at h
  rw [average_sub, average_smul, hy] at h
  simpa only [tripleHarmonicMean, matTrace, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Complex.sub_re, Complex.smul_re, Complex.natCast_re,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem four_pvm_of_nonnegative_polynomial_trace {n D : ℕ}
    (P Q R T : PVM n D) (hn : 2 ≤ n) (hD : 0 < D)
    (lam : ℝ) (hroot : MUMSpectral.quartic n lam = 0)
    (hw : lam*MUMSpectral.cubic n lam ≠ 0)
    (hPhi : 0 ≤ matTrace (matrixAverage (fun abc => omega n (tripleSum P Q R abc) *
      cubicTest n lam (tripleSum P Q R abc)))) :
    ∃ a b c d : Fin n, lam ≤ ‖selectedSum P Q R T a b c d‖ := by
  apply four_pvm_of_harmonic_bound P Q R T hn hD lam
  intro hres
  exact (harmonic_trace_deficit P Q R (by omega) lam hroot hw hres).trans
    (sub_le_self _ (div_nonneg hPhi (sq_nonneg _)))

end Harmonic
end

section
open scoped BigOperators Matrix ComplexOrder
open MUMSpectral FourMeasScalars
namespace FourMeas
noncomputable section

def Phi {n D : ℕ} (P Q R : PVM n D) (lam : ℝ) : ℝ :=
  (∑ a, ∑ b, ∑ c,
    matTrace (Harmonic.omega n (P.proj a+Q.proj b+R.proj c) *
      Harmonic.cubicTest n lam (P.proj a+Q.proj b+R.proj c))) / (n : ℝ)^3

theorem trace_omega_cubicTest (n D : ℕ) (lam : ℝ) (S : Mat D) :
    matTrace (Harmonic.omega n S * Harmonic.cubicTest n lam S) =
    coeff1 n lam * matTrace S + coeff2 n lam * matTrace (S^2) +
    coeff3 n lam * matTrace (S^3) + coeff4 n lam * matTrace (S^4) +
    coeff5 n lam * matTrace (S^5) + coeff6 lam * matTrace (S^6) + matTrace (S^7) := by
  unfold Harmonic.omega Harmonic.cubicTest coeff1 coeff2 coeff3 coeff4 coeff5 coeff6
  unfold MUMSpectral.cubic SpectralPolynomialBounds.originalCubic
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, sub_mul,
    mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc,
    matTrace, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    Complex.add_re, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  ring

theorem Phi_eq_moments {n D : ℕ} (P Q R : PVM n D) (lam : ℝ) :
    Phi P Q R lam = coeff1 n lam * moment P Q R 1 +
    coeff2 n lam * moment P Q R 2 + coeff3 n lam * moment P Q R 3 +
    coeff4 n lam * moment P Q R 4 + coeff5 n lam * moment P Q R 5 +
    coeff6 lam * moment P Q R 6 + moment P Q R 7 := by
  unfold Phi
  simp_rw [trace_omega_cubicTest]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold moment
  simp only [pow_one]
  ring

theorem Phi_eq_average {n D : ℕ} (P Q R : PVM n D) (lam : ℝ) :
    Phi P Q R lam = matTrace (matrixAverage fun abc =>
      Harmonic.omega n (tripleSum P Q R abc) *
        Harmonic.cubicTest n lam (tripleSum P Q R abc)) := by
  unfold Phi matTrace matrixAverage tripleSum
  simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Matrix.trace_sum,
    Complex.re_sum, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Fintype.sum_prod_type]
  ring

end
end FourMeas
end

section
open scoped BigOperators Matrix ComplexConjugate
open MUMSpectral

namespace PairTraceIdentities

theorem sandwich_trace {D : ℕ} (p x : Mat D) (hp : p * p = p) :
    Matrix.trace (p * x * p) = Matrix.trace (p * x) := by
  rw [Matrix.trace_mul_comm (p * x) p, ← mul_assoc, hp]

theorem centered_sandwich_square {D : ℕ} (p x : Mat D) (u : ℝ)
    (hp : p * p = p) :
    matTrace ((p * x * p - u • p)^2) =
      matTrace (p * x * p * x) - 2 * u * matTrace (p * x) +
        u^2 * matTrace p := by
  have hs : Matrix.trace (p * x * p) = Matrix.trace (p * x) :=
    sandwich_trace p x hp
  have hsq : Matrix.trace ((p * x * p) * (p * x * p)) =
      Matrix.trace (p * x * p * x) := by
    have hm : (p * x * p) * (p * x * p) = p * (x * p * x) * p := by
      calc
        _ = p * x * (p * p) * x * p := by noncomm_ring
        _ = _ := by rw [hp]; noncomm_ring
    rw [hm, sandwich_trace p (x * p * x) hp]
    simp only [mul_assoc]
  have hl : p * (p * x * p) = p * x * p := by
    simp only [← mul_assoc, hp]
  have hr : (p * x * p) * p = p * x * p := by
    simp only [mul_assoc, hp]
  simp only [pow_two, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, hp, hl, hr, matTrace, Matrix.trace_sub, Matrix.trace_smul,
    hsq, hs, Complex.sub_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  ring

theorem pair_trace_totals {n D : ℕ} (P Q : PVM n D) :
    (∑ a, ∑ b, matTrace (P.proj a * Q.proj b)) = (D : ℝ) ∧
    (∑ a, ∑ _b : Fin n, matTrace (P.proj a)) = (n : ℝ) * D := by
  constructor
  · simp only [matTrace, ← Complex.re_sum, ← Matrix.trace_sum,
      ← Finset.mul_sum, Q.complete, mul_one, P.complete]
    simp
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum, matTrace, ← Complex.re_sum,
      ← Matrix.trace_sum, P.complete]
    simp

theorem scalar_correction (n D K : ℝ) (hn : n ≠ 0) :
    K - 2 * n⁻¹ * D + (n⁻¹)^2 * (n * D) = K - D / n := by
  field_simp
  ring

theorem pair_energy_identity (n D : ℕ) (hn : 0 < n) (P Q : PVM n D) :
    (∑ a, ∑ b, matTrace ((P.proj a * Q.proj b * P.proj a -
      (n : ℝ)⁻¹ • P.proj a)^2)) =
    (∑ a, ∑ b, matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b)) -
      (D : ℝ) / n := by
  have hp (a b : Fin n) := centered_sandwich_square
    (P.proj a) (Q.proj b) (n : ℝ)⁻¹ (P.isProj a).isIdempotentElem.eq
  simp_rw [hp]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  rw [(pair_trace_totals P Q).1]
  have hrepeat := (pair_trace_totals P Q).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at hrepeat ⊢
  rw [hrepeat]
  exact scalar_correction n D _ (by exact_mod_cast Nat.ne_of_gt hn)

end PairTraceIdentities
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral

theorem pairSigma_eq_alternating {n D : ℕ} (hn : 0 < n) (P Q : PVM n D) :
    pairSigma P Q =
      (∑ a, ∑ b, matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b)) -
        (D : ℝ) / n := by
  exact PairTraceIdentities.pair_energy_identity n D hn P Q

set_option maxHeartbeats 2000000 in
theorem pairSigma_symm {n D : ℕ} (P Q : PVM n D) : pairSigma P Q = pairSigma Q P := by
  by_cases hn : n = 0
  · subst n
    simp only [pairSigma, Finset.univ_eq_empty, Finset.sum_empty]
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  rw [pairSigma_eq_alternating hn', pairSigma_eq_alternating hn']
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  unfold matTrace
  congr 1
  calc
    Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b) =
        Matrix.trace (P.proj a * (Q.proj b * P.proj a * Q.proj b)) := by simp only [mul_assoc]
    _ = Matrix.trace ((Q.proj b * P.proj a * Q.proj b) * P.proj a) :=
      Matrix.trace_mul_comm _ _

end FourMeas
end

section
open scoped BigOperators
namespace FourMeasWords
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
variable {D : ℕ} (p q r : MUMSpectral.Mat D)
variable (hp : p*p=p) (hq : q*q=q) (hr : r*r=r)
private theorem aux4_idem_tail (a b : MUMSpectral.Mat D) (h : a*a=a) : a*(a*b)=a*b := by
  rw [← mul_assoc,h]
include hp hq hr

theorem cyclic_qp : Matrix.trace (q*p) = Matrix.trace (p*q) := by
  calc
    Matrix.trace (q*p) = Matrix.trace (p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p)

theorem cyclic_rp : Matrix.trace (r*p) = Matrix.trace (p*r) := by
  calc
    Matrix.trace (r*p) = Matrix.trace (p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p)

theorem cyclic_rq : Matrix.trace (r*q) = Matrix.trace (q*r) := by
  calc
    Matrix.trace (r*q) = Matrix.trace (q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q)

theorem cyclic_pqp : Matrix.trace (p*q*p) = Matrix.trace (p*q) := by
  calc
    Matrix.trace (p*q*p) = Matrix.trace (q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p)
    _ = Matrix.trace (q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p) = Matrix.trace (p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p)

theorem cyclic_prp : Matrix.trace (p*r*p) = Matrix.trace (p*r) := by
  calc
    Matrix.trace (p*r*p) = Matrix.trace (r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p)
    _ = Matrix.trace (r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p) = Matrix.trace (p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p)

theorem cyclic_qpq : Matrix.trace (q*p*q) = Matrix.trace (p*q) := by
  calc
    Matrix.trace (q*p*q) = Matrix.trace (p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q)
    _ = Matrix.trace (p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpr : Matrix.trace (q*p*r) = Matrix.trace (p*r*q) := by
  calc
    Matrix.trace (q*p*r) = Matrix.trace (p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r)

theorem cyclic_qrp : Matrix.trace (q*r*p) = Matrix.trace (p*q*r) := by
  calc
    Matrix.trace (q*r*p) = Matrix.trace (r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p)
    Matrix.trace (r*p*q) = Matrix.trace (p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q)

theorem cyclic_qrq : Matrix.trace (q*r*q) = Matrix.trace (q*r) := by
  calc
    Matrix.trace (q*r*q) = Matrix.trace (r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q)
    _ = Matrix.trace (r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q) = Matrix.trace (q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q)

theorem cyclic_rpq : Matrix.trace (r*p*q) = Matrix.trace (p*q*r) := by
  calc
    Matrix.trace (r*p*q) = Matrix.trace (p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q)

theorem cyclic_rpr : Matrix.trace (r*p*r) = Matrix.trace (p*r) := by
  calc
    Matrix.trace (r*p*r) = Matrix.trace (p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r)
    _ = Matrix.trace (p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rqp : Matrix.trace (r*q*p) = Matrix.trace (p*r*q) := by
  calc
    Matrix.trace (r*q*p) = Matrix.trace (q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p)
    Matrix.trace (q*p*r) = Matrix.trace (p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r)

theorem cyclic_rqr : Matrix.trace (r*q*r) = Matrix.trace (q*r) := by
  calc
    Matrix.trace (r*q*r) = Matrix.trace (q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r)
    _ = Matrix.trace (q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_pqrp : Matrix.trace (p*q*r*p) = Matrix.trace (p*q*r) := by
  calc
    Matrix.trace (p*q*r*p) = Matrix.trace (q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p)
    _ = Matrix.trace (q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p) = Matrix.trace (r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p)
    Matrix.trace (r*p*q) = Matrix.trace (p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q)

theorem cyclic_prpq : Matrix.trace (p*r*p*q) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q) = Matrix.trace (r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q)
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_prqp : Matrix.trace (p*r*q*p) = Matrix.trace (p*r*q) := by
  calc
    Matrix.trace (p*r*q*p) = Matrix.trace (r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p)
    _ = Matrix.trace (r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p) = Matrix.trace (q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p)
    Matrix.trace (q*p*r) = Matrix.trace (p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r)

theorem cyclic_qpqp : Matrix.trace (q*p*q*p) = Matrix.trace (p*q*p*q) := by
  calc
    Matrix.trace (q*p*q*p) = Matrix.trace (p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p)

theorem cyclic_qpqr : Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_qprp : Matrix.trace (q*p*r*p) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p) = Matrix.trace (p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p)
    Matrix.trace (p*r*p*q) = Matrix.trace (r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q)
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_qprq : Matrix.trace (q*p*r*q) = Matrix.trace (p*r*q) := by
  calc
    Matrix.trace (q*p*r*q) = Matrix.trace (p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q)
    _ = Matrix.trace (p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qrpq : Matrix.trace (q*r*p*q) = Matrix.trace (p*q*r) := by
  calc
    Matrix.trace (q*r*p*q) = Matrix.trace (r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q)
    _ = Matrix.trace (r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q) = Matrix.trace (p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q)

theorem cyclic_qrpr : Matrix.trace (q*r*p*r) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r) = Matrix.trace (r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r)
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_qrqp : Matrix.trace (q*r*q*p) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p) = Matrix.trace (r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p)
    Matrix.trace (r*q*p*q) = Matrix.trace (q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q)
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_rpqp : Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_rpqr : Matrix.trace (r*p*q*r) = Matrix.trace (p*q*r) := by
  calc
    Matrix.trace (r*p*q*r) = Matrix.trace (p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r)
    _ = Matrix.trace (p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rprp : Matrix.trace (r*p*r*p) = Matrix.trace (p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p) = Matrix.trace (p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p)

theorem cyclic_rprq : Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_rqpq : Matrix.trace (r*q*p*q) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q) = Matrix.trace (q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q)
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_rqpr : Matrix.trace (r*q*p*r) = Matrix.trace (p*r*q) := by
  calc
    Matrix.trace (r*q*p*r) = Matrix.trace (q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r)
    _ = Matrix.trace (q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r) = Matrix.trace (p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r)

theorem cyclic_rqrp : Matrix.trace (r*q*r*p) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p) = Matrix.trace (q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p)
    Matrix.trace (q*r*p*r) = Matrix.trace (r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r)
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_rqrq : Matrix.trace (r*q*r*q) = Matrix.trace (q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q) = Matrix.trace (q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q)

theorem cyclic_pqpqp : Matrix.trace (p*q*p*q*p) = Matrix.trace (p*q*p*q) := by
  calc
    Matrix.trace (p*q*p*q*p) = Matrix.trace (q*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*p)
    _ = Matrix.trace (q*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*p) = Matrix.trace (p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p)

theorem cyclic_pqprp : Matrix.trace (p*q*p*r*p) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (p*q*p*r*p) = Matrix.trace (q*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p)
    _ = Matrix.trace (q*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*p) = Matrix.trace (p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p)
    Matrix.trace (p*r*p*q) = Matrix.trace (r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q)
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_pqrpq : Matrix.trace (p*q*r*p*q) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (p*q*r*p*q) = Matrix.trace (q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q)
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_pqrqp : Matrix.trace (p*q*r*q*p) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (p*q*r*q*p) = Matrix.trace (q*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p)
    _ = Matrix.trace (q*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*p) = Matrix.trace (r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p)
    Matrix.trace (r*q*p*q) = Matrix.trace (q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q)
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_prpqp : Matrix.trace (p*r*p*q*p) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p) = Matrix.trace (r*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p)
    _ = Matrix.trace (r*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_prpqr : Matrix.trace (p*r*p*q*r) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_prprp : Matrix.trace (p*r*p*r*p) = Matrix.trace (p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*r*p) = Matrix.trace (r*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p)
    _ = Matrix.trace (r*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*p) = Matrix.trace (p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p)

theorem cyclic_prqpq : Matrix.trace (p*r*q*p*q) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q) = Matrix.trace (r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q)
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_prqpr : Matrix.trace (p*r*q*p*r) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*r) = Matrix.trace (r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r)
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_prqrp : Matrix.trace (p*r*q*r*p) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p) = Matrix.trace (r*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p)
    _ = Matrix.trace (r*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*p) = Matrix.trace (q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p)
    Matrix.trace (q*r*p*r) = Matrix.trace (r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r)
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_qpqpq : Matrix.trace (q*p*q*p*q) = Matrix.trace (p*q*p*q) := by
  calc
    Matrix.trace (q*p*q*p*q) = Matrix.trace (p*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q)
    _ = Matrix.trace (p*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpqpr : Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_qpqrp : Matrix.trace (q*p*q*r*p) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (q*p*q*r*p) = Matrix.trace (p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p)
    Matrix.trace (p*q*r*p*q) = Matrix.trace (q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q)
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_qpqrq : Matrix.trace (q*p*q*r*q) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q) = Matrix.trace (p*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q)
    _ = Matrix.trace (p*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qprpq : Matrix.trace (q*p*r*p*q) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q) = Matrix.trace (p*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q)
    _ = Matrix.trace (p*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*q) = Matrix.trace (r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q)
    Matrix.trace (r*p*q*p) = Matrix.trace (p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p)

theorem cyclic_qprpr : Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_qprqp : Matrix.trace (q*p*r*q*p) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p) = Matrix.trace (p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p)
    Matrix.trace (p*r*q*p*q) = Matrix.trace (r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q)
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_qprqr : Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_qrpqp : Matrix.trace (q*r*p*q*p) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_qrpqr : Matrix.trace (q*r*p*q*r) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_qrprp : Matrix.trace (q*r*p*r*p) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (q*r*p*r*p) = Matrix.trace (r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p)
    Matrix.trace (r*p*r*p*q) = Matrix.trace (p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q)
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_qrprq : Matrix.trace (q*r*p*r*q) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*q) = Matrix.trace (r*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q)
    _ = Matrix.trace (r*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_qrqpq : Matrix.trace (q*r*q*p*q) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q) = Matrix.trace (r*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q)
    _ = Matrix.trace (r*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*q) = Matrix.trace (q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q)
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_qrqpr : Matrix.trace (q*r*q*p*r) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*r) = Matrix.trace (r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r)
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_qrqrp : Matrix.trace (q*r*q*r*p) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p) = Matrix.trace (r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p)
    Matrix.trace (r*q*r*p*q) = Matrix.trace (q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q)
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_qrqrq : Matrix.trace (q*r*q*r*q) = Matrix.trace (q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*q) = Matrix.trace (r*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q)
    _ = Matrix.trace (r*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*q) = Matrix.trace (q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q)

theorem cyclic_rpqpq : Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_rpqpr : Matrix.trace (r*p*q*p*r) = Matrix.trace (p*q*p*r) := by
  calc
    Matrix.trace (r*p*q*p*r) = Matrix.trace (p*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r)
    _ = Matrix.trace (p*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqrp : Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_rpqrq : Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_rprpq : Matrix.trace (r*p*r*p*q) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q) = Matrix.trace (p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q)
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_rprpr : Matrix.trace (r*p*r*p*r) = Matrix.trace (p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*r) = Matrix.trace (p*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r)
    _ = Matrix.trace (p*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rprqp : Matrix.trace (r*p*r*q*p) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p) = Matrix.trace (p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p)
    Matrix.trace (p*r*q*p*r) = Matrix.trace (r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r)
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_rprqr : Matrix.trace (r*p*r*q*r) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r) = Matrix.trace (p*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r)
    _ = Matrix.trace (p*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rqpqp : Matrix.trace (r*q*p*q*p) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_rqpqr : Matrix.trace (r*q*p*q*r) = Matrix.trace (p*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r) = Matrix.trace (q*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r)
    _ = Matrix.trace (q*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*r) = Matrix.trace (p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r)

theorem cyclic_rqprp : Matrix.trace (r*q*p*r*p) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_rqprq : Matrix.trace (r*q*p*r*q) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_rqrpq : Matrix.trace (r*q*r*p*q) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q) = Matrix.trace (q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q)
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_rqrpr : Matrix.trace (r*q*r*p*r) = Matrix.trace (p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r) = Matrix.trace (q*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r)
    _ = Matrix.trace (q*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*r) = Matrix.trace (r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r)
    Matrix.trace (r*p*r*q) = Matrix.trace (p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q)

theorem cyclic_rqrqp : Matrix.trace (r*q*r*q*p) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p) = Matrix.trace (q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p)
    Matrix.trace (q*r*q*p*r) = Matrix.trace (r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r)
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_rqrqr : Matrix.trace (r*q*r*q*r) = Matrix.trace (q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r) = Matrix.trace (q*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r)
    _ = Matrix.trace (q*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_pqpqrp : Matrix.trace (p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (p*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*r*p)
    _ = Matrix.trace (q*p*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*r*p) = Matrix.trace (p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p)
    Matrix.trace (p*q*r*p*q) = Matrix.trace (q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q)
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_pqprpq : Matrix.trace (p*q*p*r*p*q) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (p*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_pqprqp : Matrix.trace (p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (p*q*p*r*q*p) = Matrix.trace (q*p*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*q*p)
    _ = Matrix.trace (q*p*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*q*p) = Matrix.trace (p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p)
    Matrix.trace (p*r*q*p*q) = Matrix.trace (r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q)
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_pqrpqp : Matrix.trace (p*q*r*p*q*p) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (p*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p)
    _ = Matrix.trace (q*r*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_pqrprp : Matrix.trace (p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (p*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*r*p)
    _ = Matrix.trace (q*r*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*r*p) = Matrix.trace (r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p)
    Matrix.trace (r*p*r*p*q) = Matrix.trace (p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q)
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_pqrqpq : Matrix.trace (p*q*r*q*p*q) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (p*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_pqrqrp : Matrix.trace (p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (p*q*r*q*r*p) = Matrix.trace (q*r*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*r*p)
    _ = Matrix.trace (q*r*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*r*p) = Matrix.trace (r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p)
    Matrix.trace (r*q*r*p*q) = Matrix.trace (q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q)
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_prpqpq : Matrix.trace (p*r*p*q*p*q) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_prpqpr : Matrix.trace (p*r*p*q*p*r) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_prpqrp : Matrix.trace (p*r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r*p) = Matrix.trace (r*p*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p)
    _ = Matrix.trace (r*p*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_prpqrq : Matrix.trace (p*r*p*q*r*q) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_prprpq : Matrix.trace (p*r*p*r*p*q) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*r*p*q) = Matrix.trace (r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q)
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_prprqp : Matrix.trace (p*r*p*r*q*p) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*p*r*q*p) = Matrix.trace (r*p*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*p)
    _ = Matrix.trace (r*p*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*q*p) = Matrix.trace (p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p)
    Matrix.trace (p*r*q*p*r) = Matrix.trace (r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r)
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_prqpqp : Matrix.trace (p*r*q*p*q*p) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p)
    _ = Matrix.trace (r*q*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_prqpqr : Matrix.trace (p*r*q*p*q*r) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_prqprp : Matrix.trace (p*r*q*p*r*p) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*r*p) = Matrix.trace (r*q*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p)
    _ = Matrix.trace (r*q*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_prqrpq : Matrix.trace (p*r*q*r*p*q) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*q) = Matrix.trace (r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q)
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_prqrpr : Matrix.trace (p*r*q*r*p*r) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_prqrqp : Matrix.trace (p*r*q*r*q*p) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (p*r*q*r*q*p) = Matrix.trace (r*q*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*p)
    _ = Matrix.trace (r*q*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*q*p) = Matrix.trace (q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p)
    Matrix.trace (q*r*q*p*r) = Matrix.trace (r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r)
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_qpqpqp : Matrix.trace (q*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*q) := by
  calc
    Matrix.trace (q*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p)

theorem cyclic_qpqpqr : Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_qpqprp : Matrix.trace (q*p*q*p*r*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (q*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p)
    Matrix.trace (p*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_qpqprq : Matrix.trace (q*p*q*p*r*q) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q)
    _ = Matrix.trace (p*q*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpqrpq : Matrix.trace (q*p*q*r*p*q) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (q*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q)
    _ = Matrix.trace (p*q*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*q*r*p*q) = Matrix.trace (q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q)
    Matrix.trace (q*r*p*q*p) = Matrix.trace (r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p)
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_qpqrpr : Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_qpqrqp : Matrix.trace (q*p*q*r*q*p) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p)
    Matrix.trace (p*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_qpqrqr : Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_qprpqp : Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_qprpqr : Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_qprprp : Matrix.trace (q*p*r*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (q*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p)
    Matrix.trace (p*r*p*r*p*q) = Matrix.trace (r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q)
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_qprprq : Matrix.trace (q*p*r*p*r*q) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (q*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q)
    _ = Matrix.trace (p*r*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qprqpq : Matrix.trace (q*p*r*q*p*q) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p*q) = Matrix.trace (p*r*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q)
    _ = Matrix.trace (p*r*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*q*p*q) = Matrix.trace (r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q)
    Matrix.trace (r*q*p*q*p) = Matrix.trace (q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p)
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_qprqpr : Matrix.trace (q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r)

theorem cyclic_qprqrp : Matrix.trace (q*p*r*q*r*p) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (q*p*r*q*r*p) = Matrix.trace (p*r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*p)
    Matrix.trace (p*r*q*r*p*q) = Matrix.trace (r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q)
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_qprqrq : Matrix.trace (q*p*r*q*r*q) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (q*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q)
    _ = Matrix.trace (p*r*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qrpqpq : Matrix.trace (q*r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q)
    _ = Matrix.trace (r*p*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*p*q) = Matrix.trace (p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q)

theorem cyclic_qrpqpr : Matrix.trace (q*r*p*q*p*r) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_qrpqrp : Matrix.trace (q*r*p*q*r*p) = Matrix.trace (p*q*r*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r*p) = Matrix.trace (r*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p)
    Matrix.trace (r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q)

theorem cyclic_qrpqrq : Matrix.trace (q*r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q)
    _ = Matrix.trace (r*p*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_qrprpq : Matrix.trace (q*r*p*r*p*q) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (q*r*p*r*p*q) = Matrix.trace (r*p*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q)
    _ = Matrix.trace (r*p*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*p*q) = Matrix.trace (p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q)
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_qrprpr : Matrix.trace (q*r*p*r*p*r) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_qrprqp : Matrix.trace (q*r*p*r*q*p) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (q*r*p*r*q*p) = Matrix.trace (r*p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p)
    Matrix.trace (r*p*r*q*p*q) = Matrix.trace (p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q)
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_qrprqr : Matrix.trace (q*r*p*r*q*r) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_qrqpqp : Matrix.trace (q*r*q*p*q*p) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_qrqpqr : Matrix.trace (q*r*q*p*q*r) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_qrqprp : Matrix.trace (q*r*q*p*r*p) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (q*r*q*p*r*p) = Matrix.trace (r*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p)
    Matrix.trace (r*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_qrqprq : Matrix.trace (q*r*q*p*r*q) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*r*q) = Matrix.trace (r*q*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q)
    _ = Matrix.trace (r*q*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_qrqrpq : Matrix.trace (q*r*q*r*p*q) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p*q) = Matrix.trace (r*q*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q)
    _ = Matrix.trace (r*q*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*p*q) = Matrix.trace (q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q)
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_qrqrpr : Matrix.trace (q*r*q*r*p*r) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_qrqrqp : Matrix.trace (q*r*q*r*q*p) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*r*q*p) = Matrix.trace (r*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*p)
    Matrix.trace (r*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_rpqpqp : Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_rpqpqr : Matrix.trace (r*p*q*p*q*r) = Matrix.trace (p*q*p*q*r) := by
  calc
    Matrix.trace (r*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r)
    _ = Matrix.trace (p*q*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqprp : Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_rpqprq : Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_rpqrpq : Matrix.trace (r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
  calc
    Matrix.trace (r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q)

theorem cyclic_rpqrpr : Matrix.trace (r*p*q*r*p*r) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r)
    _ = Matrix.trace (p*q*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqrqp : Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_rpqrqr : Matrix.trace (r*p*q*r*q*r) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (r*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r)
    _ = Matrix.trace (p*q*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rprpqp : Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_rprpqr : Matrix.trace (r*p*r*p*q*r) = Matrix.trace (p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r)
    _ = Matrix.trace (p*r*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*q*r) = Matrix.trace (r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r)
    Matrix.trace (r*p*q*r*p) = Matrix.trace (p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p)

theorem cyclic_rprprp : Matrix.trace (r*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*p)

theorem cyclic_rprprq : Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_rprqpq : Matrix.trace (r*p*r*q*p*q) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p*q) = Matrix.trace (p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q)
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_rprqpr : Matrix.trace (r*p*r*q*p*r) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r)
    _ = Matrix.trace (p*r*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*q*p*r) = Matrix.trace (r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r)
    Matrix.trace (r*q*p*r*p) = Matrix.trace (q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p)
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_rprqrp : Matrix.trace (r*p*r*q*r*p) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r*p) = Matrix.trace (p*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*p)
    Matrix.trace (p*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_rprqrq : Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_rqpqpq : Matrix.trace (r*q*p*q*p*q) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_rqpqpr : Matrix.trace (r*q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*r) = Matrix.trace (q*p*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r)
    _ = Matrix.trace (q*p*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*p*r) = Matrix.trace (p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r)

theorem cyclic_rqpqrp : Matrix.trace (r*q*p*q*r*p) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_rqpqrq : Matrix.trace (r*q*p*q*r*q) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_rqprpq : Matrix.trace (r*q*p*r*p*q) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (r*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_rqprpr : Matrix.trace (r*q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*p*r) = Matrix.trace (q*p*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r)
    _ = Matrix.trace (q*p*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*p*r) = Matrix.trace (p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r)

theorem cyclic_rqprqp : Matrix.trace (r*q*p*r*q*p) = Matrix.trace (p*r*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q*p) = Matrix.trace (q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*p)
    Matrix.trace (q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r)

theorem cyclic_rqprqr : Matrix.trace (r*q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q*r) = Matrix.trace (q*p*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r)
    _ = Matrix.trace (q*p*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_rqrpqp : Matrix.trace (r*q*r*p*q*p) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_rqrpqr : Matrix.trace (r*q*r*p*q*r) = Matrix.trace (p*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*r) = Matrix.trace (q*r*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r)
    _ = Matrix.trace (q*r*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*q*r) = Matrix.trace (r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r)
    Matrix.trace (r*p*q*r*q) = Matrix.trace (p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q)

theorem cyclic_rqrprp : Matrix.trace (r*q*r*p*r*p) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_rqrprq : Matrix.trace (r*q*r*p*r*q) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_rqrqpq : Matrix.trace (r*q*r*q*p*q) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_rqrqpr : Matrix.trace (r*q*r*q*p*r) = Matrix.trace (p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*r) = Matrix.trace (q*r*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r)
    _ = Matrix.trace (q*r*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*p*r) = Matrix.trace (r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r)
    Matrix.trace (r*q*p*r*q) = Matrix.trace (q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q)
    Matrix.trace (q*p*r*q*r) = Matrix.trace (p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r)

theorem cyclic_rqrqrp : Matrix.trace (r*q*r*q*r*p) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r*p) = Matrix.trace (q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*p)
    Matrix.trace (q*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_rqrqrq : Matrix.trace (r*q*r*q*r*q) = Matrix.trace (q*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r*q) = Matrix.trace (q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*q)

theorem cyclic_pqpqpqp : Matrix.trace (p*q*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*q) := by
  calc
    Matrix.trace (p*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*p*q*p)
    _ = Matrix.trace (q*p*q*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p)

theorem cyclic_pqpqprp : Matrix.trace (p*q*p*q*p*r*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (p*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*p*r*p)
    _ = Matrix.trace (q*p*q*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p)
    Matrix.trace (p*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_pqpqrpq : Matrix.trace (p*q*p*q*r*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (p*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*p)
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_pqpqrqp : Matrix.trace (p*q*p*q*r*q*p) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (p*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*r*q*p)
    _ = Matrix.trace (q*p*q*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p)
    Matrix.trace (p*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_pqprpqp : Matrix.trace (p*q*p*r*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (p*q*p*r*p*q*p) = Matrix.trace (q*p*r*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*q*p)
    _ = Matrix.trace (q*p*r*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_pqprprp : Matrix.trace (p*q*p*r*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (p*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*r*p)
    _ = Matrix.trace (q*p*r*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p)
    Matrix.trace (p*r*p*r*p*q) = Matrix.trace (r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q)
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_pqprqpq : Matrix.trace (p*q*p*r*q*p*q) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (p*q*p*r*q*p*q) = Matrix.trace (q*p*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*q*p*q)
    Matrix.trace (q*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*q) = Matrix.trace (r*q*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*q)
    Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*p)
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_pqprqrp : Matrix.trace (p*q*p*r*q*r*p) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (p*q*p*r*q*r*p) = Matrix.trace (q*p*r*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*q*r*p)
    _ = Matrix.trace (q*p*r*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*q*r*p) = Matrix.trace (p*r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*p)
    Matrix.trace (p*r*q*r*p*q) = Matrix.trace (r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q)
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_pqrpqpq : Matrix.trace (p*q*r*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (p*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*p)
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_pqrpqpr : Matrix.trace (p*q*r*p*q*p*r) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (p*q*r*p*q*p*r) = Matrix.trace (q*r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*r)
    Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*p)
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_pqrpqrp : Matrix.trace (p*q*r*p*q*r*p) = Matrix.trace (p*q*r*p*q*r) := by
  calc
    Matrix.trace (p*q*r*p*q*r*p) = Matrix.trace (q*r*p*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*r*p)
    _ = Matrix.trace (q*r*p*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*q*r*p) = Matrix.trace (r*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p)
    Matrix.trace (r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q)

theorem cyclic_pqrprpq : Matrix.trace (p*q*r*p*r*p*q) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (p*q*r*p*r*p*q) = Matrix.trace (q*r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*r*p*q)
    Matrix.trace (q*r*p*r*p*q*p) = Matrix.trace (r*p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*p)
    Matrix.trace (r*p*r*p*q*p*q) = Matrix.trace (p*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p*q)
    Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_pqrprqp : Matrix.trace (p*q*r*p*r*q*p) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (p*q*r*p*r*q*p) = Matrix.trace (q*r*p*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*r*q*p)
    _ = Matrix.trace (q*r*p*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*r*q*p) = Matrix.trace (r*p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p)
    Matrix.trace (r*p*r*q*p*q) = Matrix.trace (p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q)
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_pqrqpqp : Matrix.trace (p*q*r*q*p*q*p) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (p*q*r*q*p*q*p) = Matrix.trace (q*r*q*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q*p)
    _ = Matrix.trace (q*r*q*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_pqrqpqr : Matrix.trace (p*q*r*q*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (p*q*r*q*p*q*r) = Matrix.trace (q*r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q*r)
    Matrix.trace (q*r*q*p*q*r*p) = Matrix.trace (r*q*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r*p)
    Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_pqrqprp : Matrix.trace (p*q*r*q*p*r*p) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (p*q*r*q*p*r*p) = Matrix.trace (q*r*q*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*r*p)
    _ = Matrix.trace (q*r*q*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*p*r*p) = Matrix.trace (r*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p)
    Matrix.trace (r*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_pqrqrpq : Matrix.trace (p*q*r*q*r*p*q) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (p*q*r*q*r*p*q) = Matrix.trace (q*r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*r*p*q)
    Matrix.trace (q*r*q*r*p*q*p) = Matrix.trace (r*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*p)
    Matrix.trace (r*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_pqrqrqp : Matrix.trace (p*q*r*q*r*q*p) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (p*q*r*q*r*q*p) = Matrix.trace (q*r*q*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*r*q*p)
    _ = Matrix.trace (q*r*q*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*r*q*p) = Matrix.trace (r*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*p)
    Matrix.trace (r*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_prpqpqp : Matrix.trace (p*r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*p)
    _ = Matrix.trace (r*p*q*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_prpqpqr : Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_prpqprp : Matrix.trace (p*r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*p)
    _ = Matrix.trace (r*p*q*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_prpqprq : Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*q)
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_prpqrpq : Matrix.trace (p*r*p*q*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (p*r*p*q*r*p*q) = Matrix.trace (r*p*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*q)
    Matrix.trace (r*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*r) = Matrix.trace (q*r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*r)
    Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*p)
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_prpqrpr : Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_prpqrqp : Matrix.trace (p*r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r*q*p) = Matrix.trace (r*p*q*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*p)
    _ = Matrix.trace (r*p*q*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_prpqrqr : Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_prprpqp : Matrix.trace (p*r*p*r*p*q*p) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*r*p*q*p) = Matrix.trace (r*p*r*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q*p)
    _ = Matrix.trace (r*p*r*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_prprpqr : Matrix.trace (p*r*p*r*p*q*r) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*p) = Matrix.trace (p*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*p)
    Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_prprprp : Matrix.trace (p*r*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*r) := by
  calc
    Matrix.trace (p*r*p*r*p*r*p) = Matrix.trace (r*p*r*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*r*p)
    _ = Matrix.trace (r*p*r*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*p)

theorem cyclic_prprqpq : Matrix.trace (p*r*p*r*q*p*q) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*p*r*q*p*q) = Matrix.trace (r*p*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*p*q)
    Matrix.trace (r*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*p)
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_prprqpr : Matrix.trace (p*r*p*r*q*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*p) = Matrix.trace (p*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*p)
    Matrix.trace (p*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*p)
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_prprqrp : Matrix.trace (p*r*p*r*q*r*p) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (p*r*p*r*q*r*p) = Matrix.trace (r*p*r*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*r*p)
    _ = Matrix.trace (r*p*r*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*q*r*p) = Matrix.trace (p*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*p)
    Matrix.trace (p*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_prqpqpq : Matrix.trace (p*r*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*p*q) = Matrix.trace (r*q*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*q)
    Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*p)
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_prqpqpr : Matrix.trace (p*r*q*p*q*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*p)
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_prqpqrp : Matrix.trace (p*r*q*p*q*r*p) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*r*p) = Matrix.trace (r*q*p*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r*p)
    _ = Matrix.trace (r*q*p*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_prqpqrq : Matrix.trace (p*r*q*p*q*r*q) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*q*r*q) = Matrix.trace (r*q*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r*q)
    Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*p)
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_prqprpq : Matrix.trace (p*r*q*p*r*p*q) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (p*r*q*p*r*p*q) = Matrix.trace (r*q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*q)
    Matrix.trace (r*q*p*r*p*q*p) = Matrix.trace (q*p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q*p)
    Matrix.trace (q*p*r*p*q*p*r) = Matrix.trace (p*r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p*r)
    Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*q)
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_prqprpr : Matrix.trace (p*r*q*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*p)
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_prqprqp : Matrix.trace (p*r*q*p*r*q*p) = Matrix.trace (p*r*q*p*r*q) := by
  calc
    Matrix.trace (p*r*q*p*r*q*p) = Matrix.trace (r*q*p*r*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*q*p)
    _ = Matrix.trace (r*q*p*r*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*r*q*p) = Matrix.trace (q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*p)
    Matrix.trace (q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r)

theorem cyclic_prqrpqp : Matrix.trace (p*r*q*r*p*q*p) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*q*p) = Matrix.trace (r*q*r*p*q*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q*p)
    _ = Matrix.trace (r*q*r*p*q*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_prqrpqr : Matrix.trace (p*r*q*r*p*q*r) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*p) = Matrix.trace (q*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*p)
    Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_prqrprp : Matrix.trace (p*r*q*r*p*r*p) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*r*p) = Matrix.trace (r*q*r*p*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r*p)
    _ = Matrix.trace (r*q*r*p*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_prqrprq : Matrix.trace (p*r*q*r*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*p*r*q) = Matrix.trace (r*q*r*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r*q)
    Matrix.trace (r*q*r*p*r*q*p) = Matrix.trace (q*r*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q*p)
    Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_prqrqpq : Matrix.trace (p*r*q*r*q*p*q) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (p*r*q*r*q*p*q) = Matrix.trace (r*q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*p*q)
    Matrix.trace (r*q*r*q*p*q*p) = Matrix.trace (q*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q*p)
    Matrix.trace (q*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (q*p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*q)
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_prqrqpr : Matrix.trace (p*r*q*r*q*p*r) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (p*r*q*r*q*p*r) = Matrix.trace (r*q*r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*p*r)
    Matrix.trace (r*q*r*q*p*r*p) = Matrix.trace (q*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*p)
    Matrix.trace (q*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (q*p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*q)
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_prqrqrp : Matrix.trace (p*r*q*r*q*r*p) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (p*r*q*r*q*r*p) = Matrix.trace (r*q*r*q*r*p*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*r*p)
    _ = Matrix.trace (r*q*r*q*r*p) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*q*r*p) = Matrix.trace (q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*p)
    Matrix.trace (q*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_qpqpqpq : Matrix.trace (q*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q) := by
  calc
    Matrix.trace (q*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*q)
    _ = Matrix.trace (p*q*p*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpqpqpr : Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_qpqpqrp : Matrix.trace (q*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (q*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r*p)
    Matrix.trace (p*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*p)
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_qpqpqrq : Matrix.trace (q*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r*q)
    _ = Matrix.trace (p*q*p*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpqprpq : Matrix.trace (q*p*q*p*r*p*q) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (q*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*q)
    _ = Matrix.trace (p*q*p*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_qpqprpr : Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_qpqprqp : Matrix.trace (q*p*q*p*r*q*p) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*p)
    Matrix.trace (p*q*p*r*q*p*q) = Matrix.trace (q*p*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*p*r*q*p*q)
    Matrix.trace (q*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*q) = Matrix.trace (r*q*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*q)
    Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*p)
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_qpqprqr : Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_qpqrpqp : Matrix.trace (q*p*q*r*p*q*p) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (q*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*p)
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_qpqrpqr : Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_qpqrprp : Matrix.trace (q*p*q*r*p*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (q*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r*p)
    Matrix.trace (p*q*r*p*r*p*q) = Matrix.trace (q*r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*r*p*q)
    Matrix.trace (q*r*p*r*p*q*p) = Matrix.trace (r*p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*p)
    Matrix.trace (r*p*r*p*q*p*q) = Matrix.trace (p*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p*q)
    Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_qpqrprq : Matrix.trace (q*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (q*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r*q)
    _ = Matrix.trace (p*q*r*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qpqrqpq : Matrix.trace (q*p*q*r*q*p*q) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q*p*q) = Matrix.trace (p*q*r*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*q)
    _ = Matrix.trace (p*q*r*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*p) = Matrix.trace (r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p)
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_qpqrqpr : Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_qpqrqrp : Matrix.trace (q*p*q*r*q*r*p) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (q*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r*p)
    Matrix.trace (p*q*r*q*r*p*q) = Matrix.trace (q*r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*r*p*q)
    Matrix.trace (q*r*q*r*p*q*p) = Matrix.trace (r*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*p)
    Matrix.trace (r*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_qpqrqrq : Matrix.trace (q*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r*q)
    _ = Matrix.trace (p*q*r*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qprpqpq : Matrix.trace (q*p*r*p*q*p*q) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q*p*q) = Matrix.trace (p*r*p*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p*q)
    _ = Matrix.trace (p*r*p*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*q*p*q) = Matrix.trace (r*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q)
    Matrix.trace (r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p)

theorem cyclic_qprpqpr : Matrix.trace (q*p*r*p*q*p*r) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q*p*r) = Matrix.trace (p*r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p*r)
    Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*q)
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_qprpqrp : Matrix.trace (q*p*r*p*q*r*p) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (q*p*r*p*q*r*p) = Matrix.trace (p*r*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r*p)
    Matrix.trace (p*r*p*q*r*p*q) = Matrix.trace (r*p*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*q)
    Matrix.trace (r*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*r) = Matrix.trace (q*r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*r)
    Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*p)
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_qprpqrq : Matrix.trace (q*p*r*p*q*r*q) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (q*p*r*p*q*r*q) = Matrix.trace (p*r*p*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r*q)
    _ = Matrix.trace (p*r*p*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_qprprpq : Matrix.trace (q*p*r*p*r*p*q) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (q*p*r*p*r*p*q) = Matrix.trace (p*r*p*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*q)
    _ = Matrix.trace (p*r*p*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*r*p*q) = Matrix.trace (r*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q)
    Matrix.trace (r*p*r*p*q*p) = Matrix.trace (p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p)
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_qprprpr : Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_qprprqp : Matrix.trace (q*p*r*p*r*q*p) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (q*p*r*p*r*q*p) = Matrix.trace (p*r*p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*p)
    Matrix.trace (p*r*p*r*q*p*q) = Matrix.trace (r*p*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*p*q)
    Matrix.trace (r*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*p)
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_qprprqr : Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_qprqpqp : Matrix.trace (q*p*r*q*p*q*p) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*q) = Matrix.trace (r*q*p*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*q)
    Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*p)
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_qprqpqr : Matrix.trace (q*p*r*q*p*q*r) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p*q*r) = Matrix.trace (p*r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*r)
    Matrix.trace (p*r*q*p*q*r*q) = Matrix.trace (r*q*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r*q)
    Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*p)
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_qprqprp : Matrix.trace (q*p*r*q*p*r*p) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (q*p*r*q*p*r*p) = Matrix.trace (p*r*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r*p)
    Matrix.trace (p*r*q*p*r*p*q) = Matrix.trace (r*q*p*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*q)
    Matrix.trace (r*q*p*r*p*q*p) = Matrix.trace (q*p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q*p)
    Matrix.trace (q*p*r*p*q*p*r) = Matrix.trace (p*r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p*r)
    Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*q)
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_qprqprq : Matrix.trace (q*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q) := by
  calc
    Matrix.trace (q*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r*q)
    _ = Matrix.trace (p*r*q*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_qprqrpq : Matrix.trace (q*p*r*q*r*p*q) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (q*p*r*q*r*p*q) = Matrix.trace (p*r*q*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*p*q)
    _ = Matrix.trace (p*r*q*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*q*r*p*q) = Matrix.trace (r*q*r*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q)
    Matrix.trace (r*q*r*p*q*p) = Matrix.trace (q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p)
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_qprqrpr : Matrix.trace (q*p*r*q*r*p*r) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (q*p*r*q*r*p*r) = Matrix.trace (p*r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*p*r)
    Matrix.trace (p*r*q*r*p*r*q) = Matrix.trace (r*q*r*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r*q)
    Matrix.trace (r*q*r*p*r*q*p) = Matrix.trace (q*r*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q*p)
    Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_qprqrqp : Matrix.trace (q*p*r*q*r*q*p) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (q*p*r*q*r*q*p) = Matrix.trace (p*r*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*p)
    Matrix.trace (p*r*q*r*q*p*q) = Matrix.trace (r*q*r*q*p*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*p*q)
    Matrix.trace (r*q*r*q*p*q*p) = Matrix.trace (q*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q*p)
    Matrix.trace (q*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (q*p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*q)
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_qprqrqr : Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_qrpqpqp : Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*q*p) = Matrix.trace (r*p*q*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*p)
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_qrpqpqr : Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_qrpqprp : Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*p)
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_qrpqprq : Matrix.trace (q*r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*q)
    _ = Matrix.trace (r*p*q*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_qrpqrpq : Matrix.trace (q*r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r*p*q) = Matrix.trace (r*p*q*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*q)
    _ = Matrix.trace (r*p*q*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q)

theorem cyclic_qrpqrpr : Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_qrpqrqp : Matrix.trace (q*r*p*q*r*q*p) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (q*r*p*q*r*q*p) = Matrix.trace (r*p*q*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*p)
    Matrix.trace (r*p*q*r*q*p*q) = Matrix.trace (p*q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p*q)
    Matrix.trace (p*q*r*q*p*q*r) = Matrix.trace (q*r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q*r)
    Matrix.trace (q*r*q*p*q*r*p) = Matrix.trace (r*q*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r*p)
    Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_qrpqrqr : Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_qrprpqp : Matrix.trace (q*r*p*r*p*q*p) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (q*r*p*r*p*q*p) = Matrix.trace (r*p*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*p)
    Matrix.trace (r*p*r*p*q*p*q) = Matrix.trace (p*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p*q)
    Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_qrprpqr : Matrix.trace (q*r*p*r*p*q*r) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (q*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*q) = Matrix.trace (p*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*q)
    Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_qrprprp : Matrix.trace (q*r*p*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (q*r*p*r*p*r*p) = Matrix.trace (r*p*r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r*p)
    Matrix.trace (r*p*r*p*r*p*q) = Matrix.trace (p*r*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*p*q)
    Matrix.trace (p*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*p) = Matrix.trace (p*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*p)
    Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_qrprprq : Matrix.trace (q*r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*p*r*q) = Matrix.trace (r*p*r*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r*q)
    _ = Matrix.trace (r*p*r*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_qrprqpq : Matrix.trace (q*r*p*r*q*p*q) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (q*r*p*r*q*p*q) = Matrix.trace (r*p*r*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*q)
    _ = Matrix.trace (r*p*r*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*q*p*q) = Matrix.trace (p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q)
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_qrprqpr : Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_qrprqrp : Matrix.trace (q*r*p*r*q*r*p) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*q*r*p) = Matrix.trace (r*p*r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r*p)
    Matrix.trace (r*p*r*q*r*p*q) = Matrix.trace (p*r*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*p*q)
    Matrix.trace (p*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*p) = Matrix.trace (q*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*p)
    Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_qrprqrq : Matrix.trace (q*r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*p*r*q*r*q) = Matrix.trace (r*p*r*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r*q)
    _ = Matrix.trace (r*p*r*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_qrqpqpq : Matrix.trace (q*r*q*p*q*p*q) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*p*q) = Matrix.trace (r*q*p*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p*q)
    _ = Matrix.trace (r*q*p*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*q*p*q) = Matrix.trace (q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q)
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_qrqpqpr : Matrix.trace (q*r*q*p*q*p*r) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (q*p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*q)
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_qrqpqrp : Matrix.trace (q*r*q*p*q*r*p) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*r*p) = Matrix.trace (r*q*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r*p)
    Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_qrqpqrq : Matrix.trace (q*r*q*p*q*r*q) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*q*r*q) = Matrix.trace (r*q*p*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r*q)
    _ = Matrix.trace (r*q*p*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_qrqprpq : Matrix.trace (q*r*q*p*r*p*q) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (q*r*q*p*r*p*q) = Matrix.trace (r*q*p*r*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p*q)
    _ = Matrix.trace (r*q*p*r*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*p*r*p*q) = Matrix.trace (q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q)
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_qrqprpr : Matrix.trace (q*r*q*p*r*p*r) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (q*p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*q)
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_qrqprqp : Matrix.trace (q*r*q*p*r*q*p) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (q*r*q*p*r*q*p) = Matrix.trace (r*q*p*r*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q*p)
    Matrix.trace (r*q*p*r*q*p*q) = Matrix.trace (q*p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*p*q)
    Matrix.trace (q*p*r*q*p*q*r) = Matrix.trace (p*r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*r)
    Matrix.trace (p*r*q*p*q*r*q) = Matrix.trace (r*q*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r*q)
    Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*p)
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_qrqprqr : Matrix.trace (q*r*q*p*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*p*r*q*r) = Matrix.trace (r*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q*r)
    Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (q*p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*q)
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_qrqrpqp : Matrix.trace (q*r*q*r*p*q*p) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p*q*p) = Matrix.trace (r*q*r*p*q*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*p)
    Matrix.trace (r*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_qrqrpqr : Matrix.trace (q*r*q*r*p*q*r) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*q) = Matrix.trace (q*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*q)
    Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_qrqrprp : Matrix.trace (q*r*q*r*p*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (q*r*q*r*p*r*p) = Matrix.trace (r*q*r*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r*p)
    Matrix.trace (r*q*r*p*r*p*q) = Matrix.trace (q*r*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p*q)
    Matrix.trace (q*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*q) = Matrix.trace (p*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*q)
    Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_qrqrprq : Matrix.trace (q*r*q*r*p*r*q) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*p*r*q) = Matrix.trace (r*q*r*p*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r*q)
    _ = Matrix.trace (r*q*r*p*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_qrqrqpq : Matrix.trace (q*r*q*r*q*p*q) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*r*q*p*q) = Matrix.trace (r*q*r*q*p*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*p*q)
    _ = Matrix.trace (r*q*r*q*p*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*q*p*q) = Matrix.trace (q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q)
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_qrqrqpr : Matrix.trace (q*r*q*r*q*p*r) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (q*r*q*r*q*p*r) = Matrix.trace (r*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*p*r)
    Matrix.trace (r*q*r*q*p*r*q) = Matrix.trace (q*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*q)
    Matrix.trace (q*r*q*p*r*q*r) = Matrix.trace (r*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q*r)
    Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (q*p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*q)
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_qrqrqrp : Matrix.trace (q*r*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*q*r*p) = Matrix.trace (r*q*r*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*r*p)
    Matrix.trace (r*q*r*q*r*p*q) = Matrix.trace (q*r*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*p*q)
    Matrix.trace (q*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*q) = Matrix.trace (q*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*q)
    Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_qrqrqrq : Matrix.trace (q*r*q*r*q*r*q) = Matrix.trace (q*r*q*r*q*r) := by
  calc
    Matrix.trace (q*r*q*r*q*r*q) = Matrix.trace (r*q*r*q*r*q*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*r*q)
    _ = Matrix.trace (r*q*r*q*r*q) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (r*q*r*q*r*q) = Matrix.trace (q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*q)

theorem cyclic_rpqpqpq : Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
  calc
    Matrix.trace (r*p*q*p*q*p*q) = Matrix.trace (p*q*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*q)

theorem cyclic_rpqpqpr : Matrix.trace (r*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r) := by
  calc
    Matrix.trace (r*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*p*r)
    _ = Matrix.trace (p*q*p*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqpqrp : Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_rpqpqrq : Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_rpqprpq : Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_rpqprpr : Matrix.trace (r*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (r*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*r)
    _ = Matrix.trace (p*q*p*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqprqp : Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_rpqprqr : Matrix.trace (r*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (r*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*r)
    _ = Matrix.trace (p*q*p*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqrpqp : Matrix.trace (r*p*q*r*p*q*p) = Matrix.trace (p*q*p*r*p*q*r) := by
  calc
    Matrix.trace (r*p*q*r*p*q*p) = Matrix.trace (p*q*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q*p)
    Matrix.trace (p*q*r*p*q*p*r) = Matrix.trace (q*r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*p*q*p*r)
    Matrix.trace (q*r*p*q*p*r*p) = Matrix.trace (r*p*q*p*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r*p)
    Matrix.trace (r*p*q*p*r*p*q) = Matrix.trace (p*q*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p*q)

theorem cyclic_rpqrpqr : Matrix.trace (r*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r) := by
  calc
    Matrix.trace (r*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*q*r)
    _ = Matrix.trace (p*q*r*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqrprp : Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_rpqrprq : Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_rpqrqpq : Matrix.trace (r*p*q*r*q*p*q) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (r*p*q*r*q*p*q) = Matrix.trace (p*q*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p*q)
    Matrix.trace (p*q*r*q*p*q*r) = Matrix.trace (q*r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (q*r*q*p*q*r)
    Matrix.trace (q*r*q*p*q*r*p) = Matrix.trace (r*q*p*q*r*p*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r*p)
    Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_rpqrqpr : Matrix.trace (r*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (r*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p*r)
    _ = Matrix.trace (p*q*r*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rpqrqrp : Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_rpqrqrq : Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_rprpqpq : Matrix.trace (r*p*r*p*q*p*q) = Matrix.trace (p*q*p*q*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*p*q) = Matrix.trace (p*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p*q)
    Matrix.trace (p*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*p) = Matrix.trace (p*q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*p)

theorem cyclic_rprpqpr : Matrix.trace (r*p*r*p*q*p*r) = Matrix.trace (p*q*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*p*r) = Matrix.trace (p*r*p*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*p*r)
    _ = Matrix.trace (p*r*p*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*p)

theorem cyclic_rprpqrp : Matrix.trace (r*p*r*p*q*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*r*p) = Matrix.trace (p*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*p)
    Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_rprpqrq : Matrix.trace (r*p*r*p*q*r*q) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*q*r*q) = Matrix.trace (p*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*q)
    Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_rprprpq : Matrix.trace (r*p*r*p*r*p*q) = Matrix.trace (p*q*r*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*r*p*q) = Matrix.trace (p*r*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*p*q)
    Matrix.trace (p*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*p) = Matrix.trace (p*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*p)
    Matrix.trace (p*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*p) = Matrix.trace (p*q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*p)

theorem cyclic_rprprpr : Matrix.trace (r*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r) := by
  calc
    Matrix.trace (r*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*p*r)
    _ = Matrix.trace (p*r*p*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rprprqp : Matrix.trace (r*p*r*p*r*q*p) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*p*r*q*p) = Matrix.trace (p*r*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q*p)
    Matrix.trace (p*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*p) = Matrix.trace (p*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*p)
    Matrix.trace (p*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*p)
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_rprprqr : Matrix.trace (r*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q*r)
    _ = Matrix.trace (p*r*p*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rprqpqp : Matrix.trace (r*p*r*q*p*q*p) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p*q*p) = Matrix.trace (p*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q*p)
    Matrix.trace (p*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*p)
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_rprqpqr : Matrix.trace (r*p*r*q*p*q*r) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p*q*r) = Matrix.trace (p*r*q*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*q*r)
    _ = Matrix.trace (p*r*q*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*p) = Matrix.trace (q*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p)
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_rprqprp : Matrix.trace (r*p*r*q*p*r*p) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (r*p*r*q*p*r*p) = Matrix.trace (p*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*p)
    Matrix.trace (p*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*p)
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_rprqprq : Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_rprqrpq : Matrix.trace (r*p*r*q*r*p*q) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r*p*q) = Matrix.trace (p*r*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*p*q)
    Matrix.trace (p*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*p) = Matrix.trace (q*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*p)
    Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_rprqrpr : Matrix.trace (r*p*r*q*r*p*r) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r*p*r) = Matrix.trace (p*r*q*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*p*r)
    _ = Matrix.trace (p*r*q*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (p*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*p) = Matrix.trace (q*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p)
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_rprqrqp : Matrix.trace (r*p*r*q*r*q*p) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (r*p*r*q*r*q*p) = Matrix.trace (p*r*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q*p)
    Matrix.trace (p*r*q*r*q*p*r) = Matrix.trace (r*q*r*q*p*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*q*p*r)
    Matrix.trace (r*q*r*q*p*r*p) = Matrix.trace (q*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*p)
    Matrix.trace (q*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (q*p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*q)
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_rprqrqr : Matrix.trace (r*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q*r)
    _ = Matrix.trace (p*r*q*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

theorem cyclic_rqpqpqp : Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (p*q*p*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*q*p) = Matrix.trace (q*p*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*p)
    Matrix.trace (q*p*q*p*q*p*r) = Matrix.trace (p*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*p*r)

theorem cyclic_rqpqpqr : Matrix.trace (r*q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*q*r) = Matrix.trace (q*p*q*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*q*r)
    _ = Matrix.trace (q*p*q*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*p*q*r) = Matrix.trace (p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*q*r)

theorem cyclic_rqpqprp : Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (p*q*p*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*r*p) = Matrix.trace (q*p*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*p)
    Matrix.trace (q*p*q*p*r*p*r) = Matrix.trace (p*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*p*r)

theorem cyclic_rqpqprq : Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (q*p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*q)
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_rqpqrpq : Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (p*q*r*p*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*p*q) = Matrix.trace (q*p*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*q)
    Matrix.trace (q*p*q*r*p*q*r) = Matrix.trace (p*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*q*r)

theorem cyclic_rqpqrpr : Matrix.trace (r*q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*p*r) = Matrix.trace (q*p*q*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*p*r)
    _ = Matrix.trace (q*p*q*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*r*p*r) = Matrix.trace (p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*p*r)

theorem cyclic_rqpqrqp : Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*p)
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_rqpqrqr : Matrix.trace (r*q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*q*r*q*r) = Matrix.trace (q*p*q*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*r)
    _ = Matrix.trace (q*p*q*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_rqprpqp : Matrix.trace (r*q*p*r*p*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
  calc
    Matrix.trace (r*q*p*r*p*q*p) = Matrix.trace (q*p*r*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q*p)
    Matrix.trace (q*p*r*p*q*p*r) = Matrix.trace (p*r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*p*r)
    Matrix.trace (p*r*p*q*p*r*q) = Matrix.trace (r*p*q*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*p*r*q)
    Matrix.trace (r*p*q*p*r*q*p) = Matrix.trace (p*q*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q*p)

theorem cyclic_rqprpqr : Matrix.trace (r*q*p*r*p*q*r) = Matrix.trace (p*q*r*q*p*r) := by
  calc
    Matrix.trace (r*q*p*r*p*q*r) = Matrix.trace (q*p*r*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*q*r)
    _ = Matrix.trace (q*p*r*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*p*q*r) = Matrix.trace (p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*q*r)
    Matrix.trace (p*r*p*q*r*q) = Matrix.trace (r*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q)
    Matrix.trace (r*p*q*r*q*p) = Matrix.trace (p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*p)

theorem cyclic_rqprprp : Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (p*r*p*r*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*p*r*p) = Matrix.trace (q*p*r*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*p)
    Matrix.trace (q*p*r*p*r*p*r) = Matrix.trace (p*r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*p*r)

theorem cyclic_rqprprq : Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (q*p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*q)
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_rqprqpq : Matrix.trace (r*q*p*r*q*p*q) = Matrix.trace (p*q*r*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q*p*q) = Matrix.trace (q*p*r*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*p*q)
    Matrix.trace (q*p*r*q*p*q*r) = Matrix.trace (p*r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*q*r)
    Matrix.trace (p*r*q*p*q*r*q) = Matrix.trace (r*q*p*q*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*p*q*r*q)
    Matrix.trace (r*q*p*q*r*q*p) = Matrix.trace (q*p*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q*p)
    Matrix.trace (q*p*q*r*q*p*r) = Matrix.trace (p*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*p*r)

theorem cyclic_rqprqpr : Matrix.trace (r*q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q*p*r) = Matrix.trace (q*p*r*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*p*r)
    _ = Matrix.trace (q*p*r*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*p*r*q*p*r) = Matrix.trace (p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*p*r)

theorem cyclic_rqprqrp : Matrix.trace (r*q*p*r*q*r*p) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (r*q*p*r*q*r*p) = Matrix.trace (q*p*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*p)
    Matrix.trace (q*p*r*q*r*p*r) = Matrix.trace (p*r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*p*r)
    Matrix.trace (p*r*q*r*p*r*q) = Matrix.trace (r*q*r*p*r*q*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*q*r*p*r*q)
    Matrix.trace (r*q*r*p*r*q*p) = Matrix.trace (q*r*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q*p)
    Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_rqprqrq : Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (q*p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*q)
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_rqrpqpq : Matrix.trace (r*q*r*p*q*p*q) = Matrix.trace (p*q*p*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*p*q) = Matrix.trace (q*r*p*q*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p*q)
    Matrix.trace (q*r*p*q*p*q*r) = Matrix.trace (r*p*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*q*r)
    Matrix.trace (r*p*q*p*q*r*q) = Matrix.trace (p*q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*q*r*q)

theorem cyclic_rqrpqpr : Matrix.trace (r*q*r*p*q*p*r) = Matrix.trace (p*q*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*p*r) = Matrix.trace (q*r*p*q*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*p*r)
    _ = Matrix.trace (q*r*p*q*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*q*p*r) = Matrix.trace (r*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*p*r)
    Matrix.trace (r*p*q*p*r*q) = Matrix.trace (p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*p*r*q)

theorem cyclic_rqrpqrp : Matrix.trace (r*q*r*p*q*r*p) = Matrix.trace (p*q*r*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*r*p) = Matrix.trace (q*r*p*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*p)
    Matrix.trace (q*r*p*q*r*p*r) = Matrix.trace (r*p*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*p*r)
    Matrix.trace (r*p*q*r*p*r*q) = Matrix.trace (p*q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*p*r*q)

theorem cyclic_rqrpqrq : Matrix.trace (r*q*r*p*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*q*r*q) = Matrix.trace (q*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*q)
    Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_rqrprpq : Matrix.trace (r*q*r*p*r*p*q) = Matrix.trace (p*q*r*q*r*p*r) := by
  calc
    Matrix.trace (r*q*r*p*r*p*q) = Matrix.trace (q*r*p*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p*q)
    Matrix.trace (q*r*p*r*p*q*r) = Matrix.trace (r*p*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*q*r)
    Matrix.trace (r*p*r*p*q*r*q) = Matrix.trace (p*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*q*r*q)
    Matrix.trace (p*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*p) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm p (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*p) = Matrix.trace (p*q*r*q*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*p)

theorem cyclic_rqrprpr : Matrix.trace (r*q*r*p*r*p*r) = Matrix.trace (p*r*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r*p*r) = Matrix.trace (q*r*p*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*p*r)
    _ = Matrix.trace (q*r*p*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*r*p*r) = Matrix.trace (r*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*p*r)
    Matrix.trace (r*p*r*p*r*q) = Matrix.trace (p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*p*r*q)

theorem cyclic_rqrprqp : Matrix.trace (r*q*r*p*r*q*p) = Matrix.trace (p*r*q*p*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r*q*p) = Matrix.trace (q*r*p*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q*p)
    Matrix.trace (q*r*p*r*q*p*r) = Matrix.trace (r*p*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*p*r)
    Matrix.trace (r*p*r*q*p*r*q) = Matrix.trace (p*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*p*r*q)

theorem cyclic_rqrprqr : Matrix.trace (r*q*r*p*r*q*r) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*p*r*q*r) = Matrix.trace (q*r*p*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q*r)
    _ = Matrix.trace (q*r*p*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_rqrqpqp : Matrix.trace (r*q*r*q*p*q*p) = Matrix.trace (p*q*p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*q*p) = Matrix.trace (q*r*q*p*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q*p)
    Matrix.trace (q*r*q*p*q*p*r) = Matrix.trace (r*q*p*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*p*r)
    Matrix.trace (r*q*p*q*p*r*q) = Matrix.trace (q*p*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*p*r*q)
    Matrix.trace (q*p*q*p*r*q*r) = Matrix.trace (p*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*p*r*q*r)

theorem cyclic_rqrqpqr : Matrix.trace (r*q*r*q*p*q*r) = Matrix.trace (p*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*q*r) = Matrix.trace (q*r*q*p*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*q*r)
    _ = Matrix.trace (q*r*q*p*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*p*q*r) = Matrix.trace (r*q*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*q*r)
    Matrix.trace (r*q*p*q*r*q) = Matrix.trace (q*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*q*r*q)
    Matrix.trace (q*p*q*r*q*r) = Matrix.trace (p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*q*r*q*r)

theorem cyclic_rqrqprp : Matrix.trace (r*q*r*q*p*r*p) = Matrix.trace (p*r*p*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*r*p) = Matrix.trace (q*r*q*p*r*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*p)
    Matrix.trace (q*r*q*p*r*p*r) = Matrix.trace (r*q*p*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*p*r)
    Matrix.trace (r*q*p*r*p*r*q) = Matrix.trace (q*p*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*p*r*q)
    Matrix.trace (q*p*r*p*r*q*r) = Matrix.trace (p*r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*p*r*q*r)

theorem cyclic_rqrqprq : Matrix.trace (r*q*r*q*p*r*q) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*p*r*q) = Matrix.trace (q*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*q)
    Matrix.trace (q*r*q*p*r*q*r) = Matrix.trace (r*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q*r)
    Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (q*p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*q)
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_rqrqrpq : Matrix.trace (r*q*r*q*r*p*q) = Matrix.trace (p*q*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r*p*q) = Matrix.trace (q*r*q*r*p*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*p*q)
    Matrix.trace (q*r*q*r*p*q*r) = Matrix.trace (r*q*r*p*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*q*r)
    Matrix.trace (r*q*r*p*q*r*q) = Matrix.trace (q*r*p*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*q*r*q)
    Matrix.trace (q*r*p*q*r*q*r) = Matrix.trace (r*p*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*q*r*q*r)
    Matrix.trace (r*p*q*r*q*r*q) = Matrix.trace (p*q*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*q*r*q*r*q)

theorem cyclic_rqrqrpr : Matrix.trace (r*q*r*q*r*p*r) = Matrix.trace (p*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r*p*r) = Matrix.trace (q*r*q*r*p*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*p*r)
    _ = Matrix.trace (q*r*q*r*p*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
    Matrix.trace (q*r*q*r*p*r) = Matrix.trace (r*q*r*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*p*r)
    Matrix.trace (r*q*r*p*r*q) = Matrix.trace (q*r*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*p*r*q)
    Matrix.trace (q*r*p*r*q*r) = Matrix.trace (r*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*p*r*q*r)
    Matrix.trace (r*p*r*q*r*q) = Matrix.trace (p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (p*r*q*r*q)

theorem cyclic_rqrqrqp : Matrix.trace (r*q*r*q*r*q*p) = Matrix.trace (p*r*q*r*q*r*q) := by
  calc
    Matrix.trace (r*q*r*q*r*q*p) = Matrix.trace (q*r*q*r*q*p*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*q*p)
    Matrix.trace (q*r*q*r*q*p*r) = Matrix.trace (r*q*r*q*p*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*r*q*p*r)
    Matrix.trace (r*q*r*q*p*r*q) = Matrix.trace (q*r*q*p*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*p*r*q)
    Matrix.trace (q*r*q*p*r*q*r) = Matrix.trace (r*q*p*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (r*q*p*r*q*r)
    Matrix.trace (r*q*p*r*q*r*q) = Matrix.trace (q*p*r*q*r*q*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*p*r*q*r*q)
    Matrix.trace (q*p*r*q*r*q*r) = Matrix.trace (p*r*q*r*q*r*q) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm q (p*r*q*r*q*r)

theorem cyclic_rqrqrqr : Matrix.trace (r*q*r*q*r*q*r) = Matrix.trace (q*r*q*r*q*r) := by
  calc
    Matrix.trace (r*q*r*q*r*q*r) = Matrix.trace (q*r*q*r*q*r*r) := by
      simpa only [mul_assoc] using Matrix.trace_mul_comm r (q*r*q*r*q*r)
    _ = Matrix.trace (q*r*q*r*q*r) := by
      simp only [mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_1 : Matrix.trace ((p+q+r)^1) =
    (1 : ℂ) * Matrix.trace (p) +
    (1 : ℂ) * Matrix.trace (q) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals skip
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_2 : Matrix.trace ((p+q+r)^2) =
    (1 : ℂ) * Matrix.trace (p) +
    (2 : ℂ) * Matrix.trace (p*q) +
    (2 : ℂ) * Matrix.trace (p*r) +
    (1 : ℂ) * Matrix.trace (q) +
    (2 : ℂ) * Matrix.trace (q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr]
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_3 : Matrix.trace ((p+q+r)^3) =
    (1 : ℂ) * Matrix.trace (p) +
    (6 : ℂ) * Matrix.trace (p*q) +
    (3 : ℂ) * Matrix.trace (p*q*r) +
    (6 : ℂ) * Matrix.trace (p*r) +
    (3 : ℂ) * Matrix.trace (p*r*q) +
    (1 : ℂ) * Matrix.trace (q) +
    (6 : ℂ) * Matrix.trace (q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr,
    cyclic_pqp p q r hp hq hr,
    cyclic_prp p q r hp hq hr,
    cyclic_qpq p q r hp hq hr,
    cyclic_qpr p q r hp hq hr,
    cyclic_qrp p q r hp hq hr,
    cyclic_qrq p q r hp hq hr,
    cyclic_rpq p q r hp hq hr,
    cyclic_rpr p q r hp hq hr,
    cyclic_rqp p q r hp hq hr,
    cyclic_rqr p q r hp hq hr]
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_4 : Matrix.trace ((p+q+r)^4) =
    (1 : ℂ) * Matrix.trace (p) +
    (12 : ℂ) * Matrix.trace (p*q) +
    (2 : ℂ) * Matrix.trace (p*q*p*q) +
    (4 : ℂ) * Matrix.trace (p*q*p*r) +
    (12 : ℂ) * Matrix.trace (p*q*r) +
    (4 : ℂ) * Matrix.trace (p*q*r*q) +
    (12 : ℂ) * Matrix.trace (p*r) +
    (2 : ℂ) * Matrix.trace (p*r*p*r) +
    (12 : ℂ) * Matrix.trace (p*r*q) +
    (4 : ℂ) * Matrix.trace (p*r*q*r) +
    (1 : ℂ) * Matrix.trace (q) +
    (12 : ℂ) * Matrix.trace (q*r) +
    (2 : ℂ) * Matrix.trace (q*r*q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr,
    cyclic_pqp p q r hp hq hr,
    cyclic_prp p q r hp hq hr,
    cyclic_qpq p q r hp hq hr,
    cyclic_qpr p q r hp hq hr,
    cyclic_qrp p q r hp hq hr,
    cyclic_qrq p q r hp hq hr,
    cyclic_rpq p q r hp hq hr,
    cyclic_rpr p q r hp hq hr,
    cyclic_rqp p q r hp hq hr,
    cyclic_rqr p q r hp hq hr,
    cyclic_pqrp p q r hp hq hr,
    cyclic_prpq p q r hp hq hr,
    cyclic_prqp p q r hp hq hr,
    cyclic_qpqp p q r hp hq hr,
    cyclic_qpqr p q r hp hq hr,
    cyclic_qprp p q r hp hq hr,
    cyclic_qprq p q r hp hq hr,
    cyclic_qrpq p q r hp hq hr,
    cyclic_qrpr p q r hp hq hr,
    cyclic_qrqp p q r hp hq hr,
    cyclic_rpqp p q r hp hq hr,
    cyclic_rpqr p q r hp hq hr,
    cyclic_rprp p q r hp hq hr,
    cyclic_rprq p q r hp hq hr,
    cyclic_rqpq p q r hp hq hr,
    cyclic_rqpr p q r hp hq hr,
    cyclic_rqrp p q r hp hq hr,
    cyclic_rqrq p q r hp hq hr]
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_5 : Matrix.trace ((p+q+r)^5) =
    (1 : ℂ) * Matrix.trace (p) +
    (20 : ℂ) * Matrix.trace (p*q) +
    (10 : ℂ) * Matrix.trace (p*q*p*q) +
    (5 : ℂ) * Matrix.trace (p*q*p*q*r) +
    (20 : ℂ) * Matrix.trace (p*q*p*r) +
    (5 : ℂ) * Matrix.trace (p*q*p*r*q) +
    (30 : ℂ) * Matrix.trace (p*q*r) +
    (5 : ℂ) * Matrix.trace (p*q*r*p*r) +
    (20 : ℂ) * Matrix.trace (p*q*r*q) +
    (5 : ℂ) * Matrix.trace (p*q*r*q*r) +
    (20 : ℂ) * Matrix.trace (p*r) +
    (10 : ℂ) * Matrix.trace (p*r*p*r) +
    (5 : ℂ) * Matrix.trace (p*r*p*r*q) +
    (30 : ℂ) * Matrix.trace (p*r*q) +
    (20 : ℂ) * Matrix.trace (p*r*q*r) +
    (5 : ℂ) * Matrix.trace (p*r*q*r*q) +
    (1 : ℂ) * Matrix.trace (q) +
    (20 : ℂ) * Matrix.trace (q*r) +
    (10 : ℂ) * Matrix.trace (q*r*q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr,
    cyclic_pqp p q r hp hq hr,
    cyclic_prp p q r hp hq hr,
    cyclic_qpq p q r hp hq hr,
    cyclic_qpr p q r hp hq hr,
    cyclic_qrp p q r hp hq hr,
    cyclic_qrq p q r hp hq hr,
    cyclic_rpq p q r hp hq hr,
    cyclic_rpr p q r hp hq hr,
    cyclic_rqp p q r hp hq hr,
    cyclic_rqr p q r hp hq hr,
    cyclic_pqrp p q r hp hq hr,
    cyclic_prpq p q r hp hq hr,
    cyclic_prqp p q r hp hq hr,
    cyclic_qpqp p q r hp hq hr,
    cyclic_qpqr p q r hp hq hr,
    cyclic_qprp p q r hp hq hr,
    cyclic_qprq p q r hp hq hr,
    cyclic_qrpq p q r hp hq hr,
    cyclic_qrpr p q r hp hq hr,
    cyclic_qrqp p q r hp hq hr,
    cyclic_rpqp p q r hp hq hr,
    cyclic_rpqr p q r hp hq hr,
    cyclic_rprp p q r hp hq hr,
    cyclic_rprq p q r hp hq hr,
    cyclic_rqpq p q r hp hq hr,
    cyclic_rqpr p q r hp hq hr,
    cyclic_rqrp p q r hp hq hr,
    cyclic_rqrq p q r hp hq hr,
    cyclic_pqpqp p q r hp hq hr,
    cyclic_pqprp p q r hp hq hr,
    cyclic_pqrpq p q r hp hq hr,
    cyclic_pqrqp p q r hp hq hr,
    cyclic_prpqp p q r hp hq hr,
    cyclic_prpqr p q r hp hq hr,
    cyclic_prprp p q r hp hq hr,
    cyclic_prqpq p q r hp hq hr,
    cyclic_prqpr p q r hp hq hr,
    cyclic_prqrp p q r hp hq hr,
    cyclic_qpqpq p q r hp hq hr,
    cyclic_qpqpr p q r hp hq hr,
    cyclic_qpqrp p q r hp hq hr,
    cyclic_qpqrq p q r hp hq hr,
    cyclic_qprpq p q r hp hq hr,
    cyclic_qprpr p q r hp hq hr,
    cyclic_qprqp p q r hp hq hr,
    cyclic_qprqr p q r hp hq hr,
    cyclic_qrpqp p q r hp hq hr,
    cyclic_qrpqr p q r hp hq hr,
    cyclic_qrprp p q r hp hq hr,
    cyclic_qrprq p q r hp hq hr,
    cyclic_qrqpq p q r hp hq hr,
    cyclic_qrqpr p q r hp hq hr,
    cyclic_qrqrp p q r hp hq hr,
    cyclic_qrqrq p q r hp hq hr,
    cyclic_rpqpq p q r hp hq hr,
    cyclic_rpqpr p q r hp hq hr,
    cyclic_rpqrp p q r hp hq hr,
    cyclic_rpqrq p q r hp hq hr,
    cyclic_rprpq p q r hp hq hr,
    cyclic_rprpr p q r hp hq hr,
    cyclic_rprqp p q r hp hq hr,
    cyclic_rprqr p q r hp hq hr,
    cyclic_rqpqp p q r hp hq hr,
    cyclic_rqpqr p q r hp hq hr,
    cyclic_rqprp p q r hp hq hr,
    cyclic_rqprq p q r hp hq hr,
    cyclic_rqrpq p q r hp hq hr,
    cyclic_rqrpr p q r hp hq hr,
    cyclic_rqrqp p q r hp hq hr,
    cyclic_rqrqr p q r hp hq hr]
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_6 : Matrix.trace ((p+q+r)^6) =
    (1 : ℂ) * Matrix.trace (p) +
    (30 : ℂ) * Matrix.trace (p*q) +
    (30 : ℂ) * Matrix.trace (p*q*p*q) +
    (2 : ℂ) * Matrix.trace (p*q*p*q*p*q) +
    (6 : ℂ) * Matrix.trace (p*q*p*q*p*r) +
    (30 : ℂ) * Matrix.trace (p*q*p*q*r) +
    (6 : ℂ) * Matrix.trace (p*q*p*q*r*q) +
    (60 : ℂ) * Matrix.trace (p*q*p*r) +
    (6 : ℂ) * Matrix.trace (p*q*p*r*p*r) +
    (30 : ℂ) * Matrix.trace (p*q*p*r*q) +
    (6 : ℂ) * Matrix.trace (p*q*p*r*q*r) +
    (60 : ℂ) * Matrix.trace (p*q*r) +
    (3 : ℂ) * Matrix.trace (p*q*r*p*q*r) +
    (30 : ℂ) * Matrix.trace (p*q*r*p*r) +
    (6 : ℂ) * Matrix.trace (p*q*r*p*r*q) +
    (60 : ℂ) * Matrix.trace (p*q*r*q) +
    (6 : ℂ) * Matrix.trace (p*q*r*q*p*r) +
    (30 : ℂ) * Matrix.trace (p*q*r*q*r) +
    (6 : ℂ) * Matrix.trace (p*q*r*q*r*q) +
    (30 : ℂ) * Matrix.trace (p*r) +
    (30 : ℂ) * Matrix.trace (p*r*p*r) +
    (2 : ℂ) * Matrix.trace (p*r*p*r*p*r) +
    (30 : ℂ) * Matrix.trace (p*r*p*r*q) +
    (6 : ℂ) * Matrix.trace (p*r*p*r*q*r) +
    (60 : ℂ) * Matrix.trace (p*r*q) +
    (3 : ℂ) * Matrix.trace (p*r*q*p*r*q) +
    (60 : ℂ) * Matrix.trace (p*r*q*r) +
    (30 : ℂ) * Matrix.trace (p*r*q*r*q) +
    (6 : ℂ) * Matrix.trace (p*r*q*r*q*r) +
    (1 : ℂ) * Matrix.trace (q) +
    (30 : ℂ) * Matrix.trace (q*r) +
    (30 : ℂ) * Matrix.trace (q*r*q*r) +
    (2 : ℂ) * Matrix.trace (q*r*q*r*q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr,
    cyclic_pqp p q r hp hq hr,
    cyclic_prp p q r hp hq hr,
    cyclic_qpq p q r hp hq hr,
    cyclic_qpr p q r hp hq hr,
    cyclic_qrp p q r hp hq hr,
    cyclic_qrq p q r hp hq hr,
    cyclic_rpq p q r hp hq hr,
    cyclic_rpr p q r hp hq hr,
    cyclic_rqp p q r hp hq hr,
    cyclic_rqr p q r hp hq hr,
    cyclic_pqrp p q r hp hq hr,
    cyclic_prpq p q r hp hq hr,
    cyclic_prqp p q r hp hq hr,
    cyclic_qpqp p q r hp hq hr,
    cyclic_qpqr p q r hp hq hr,
    cyclic_qprp p q r hp hq hr,
    cyclic_qprq p q r hp hq hr,
    cyclic_qrpq p q r hp hq hr,
    cyclic_qrpr p q r hp hq hr,
    cyclic_qrqp p q r hp hq hr,
    cyclic_rpqp p q r hp hq hr,
    cyclic_rpqr p q r hp hq hr,
    cyclic_rprp p q r hp hq hr,
    cyclic_rprq p q r hp hq hr,
    cyclic_rqpq p q r hp hq hr,
    cyclic_rqpr p q r hp hq hr,
    cyclic_rqrp p q r hp hq hr,
    cyclic_rqrq p q r hp hq hr,
    cyclic_pqpqp p q r hp hq hr,
    cyclic_pqprp p q r hp hq hr,
    cyclic_pqrpq p q r hp hq hr,
    cyclic_pqrqp p q r hp hq hr,
    cyclic_prpqp p q r hp hq hr,
    cyclic_prpqr p q r hp hq hr,
    cyclic_prprp p q r hp hq hr,
    cyclic_prqpq p q r hp hq hr,
    cyclic_prqpr p q r hp hq hr,
    cyclic_prqrp p q r hp hq hr,
    cyclic_qpqpq p q r hp hq hr,
    cyclic_qpqpr p q r hp hq hr,
    cyclic_qpqrp p q r hp hq hr,
    cyclic_qpqrq p q r hp hq hr,
    cyclic_qprpq p q r hp hq hr,
    cyclic_qprpr p q r hp hq hr,
    cyclic_qprqp p q r hp hq hr,
    cyclic_qprqr p q r hp hq hr,
    cyclic_qrpqp p q r hp hq hr,
    cyclic_qrpqr p q r hp hq hr,
    cyclic_qrprp p q r hp hq hr,
    cyclic_qrprq p q r hp hq hr,
    cyclic_qrqpq p q r hp hq hr,
    cyclic_qrqpr p q r hp hq hr,
    cyclic_qrqrp p q r hp hq hr,
    cyclic_qrqrq p q r hp hq hr,
    cyclic_rpqpq p q r hp hq hr,
    cyclic_rpqpr p q r hp hq hr,
    cyclic_rpqrp p q r hp hq hr,
    cyclic_rpqrq p q r hp hq hr,
    cyclic_rprpq p q r hp hq hr,
    cyclic_rprpr p q r hp hq hr,
    cyclic_rprqp p q r hp hq hr,
    cyclic_rprqr p q r hp hq hr,
    cyclic_rqpqp p q r hp hq hr,
    cyclic_rqpqr p q r hp hq hr,
    cyclic_rqprp p q r hp hq hr,
    cyclic_rqprq p q r hp hq hr,
    cyclic_rqrpq p q r hp hq hr,
    cyclic_rqrpr p q r hp hq hr,
    cyclic_rqrqp p q r hp hq hr,
    cyclic_rqrqr p q r hp hq hr,
    cyclic_pqpqrp p q r hp hq hr,
    cyclic_pqprpq p q r hp hq hr,
    cyclic_pqprqp p q r hp hq hr,
    cyclic_pqrpqp p q r hp hq hr,
    cyclic_pqrprp p q r hp hq hr,
    cyclic_pqrqpq p q r hp hq hr,
    cyclic_pqrqrp p q r hp hq hr,
    cyclic_prpqpq p q r hp hq hr,
    cyclic_prpqpr p q r hp hq hr,
    cyclic_prpqrp p q r hp hq hr,
    cyclic_prpqrq p q r hp hq hr,
    cyclic_prprpq p q r hp hq hr,
    cyclic_prprqp p q r hp hq hr,
    cyclic_prqpqp p q r hp hq hr,
    cyclic_prqpqr p q r hp hq hr,
    cyclic_prqprp p q r hp hq hr,
    cyclic_prqrpq p q r hp hq hr,
    cyclic_prqrpr p q r hp hq hr,
    cyclic_prqrqp p q r hp hq hr,
    cyclic_qpqpqp p q r hp hq hr,
    cyclic_qpqpqr p q r hp hq hr,
    cyclic_qpqprp p q r hp hq hr,
    cyclic_qpqprq p q r hp hq hr,
    cyclic_qpqrpq p q r hp hq hr,
    cyclic_qpqrpr p q r hp hq hr,
    cyclic_qpqrqp p q r hp hq hr,
    cyclic_qpqrqr p q r hp hq hr,
    cyclic_qprpqp p q r hp hq hr,
    cyclic_qprpqr p q r hp hq hr,
    cyclic_qprprp p q r hp hq hr,
    cyclic_qprprq p q r hp hq hr,
    cyclic_qprqpq p q r hp hq hr,
    cyclic_qprqpr p q r hp hq hr,
    cyclic_qprqrp p q r hp hq hr,
    cyclic_qprqrq p q r hp hq hr,
    cyclic_qrpqpq p q r hp hq hr,
    cyclic_qrpqpr p q r hp hq hr,
    cyclic_qrpqrp p q r hp hq hr,
    cyclic_qrpqrq p q r hp hq hr,
    cyclic_qrprpq p q r hp hq hr,
    cyclic_qrprpr p q r hp hq hr,
    cyclic_qrprqp p q r hp hq hr,
    cyclic_qrprqr p q r hp hq hr,
    cyclic_qrqpqp p q r hp hq hr,
    cyclic_qrqpqr p q r hp hq hr,
    cyclic_qrqprp p q r hp hq hr,
    cyclic_qrqprq p q r hp hq hr,
    cyclic_qrqrpq p q r hp hq hr,
    cyclic_qrqrpr p q r hp hq hr,
    cyclic_qrqrqp p q r hp hq hr,
    cyclic_rpqpqp p q r hp hq hr,
    cyclic_rpqpqr p q r hp hq hr,
    cyclic_rpqprp p q r hp hq hr,
    cyclic_rpqprq p q r hp hq hr,
    cyclic_rpqrpq p q r hp hq hr,
    cyclic_rpqrpr p q r hp hq hr,
    cyclic_rpqrqp p q r hp hq hr,
    cyclic_rpqrqr p q r hp hq hr,
    cyclic_rprpqp p q r hp hq hr,
    cyclic_rprpqr p q r hp hq hr,
    cyclic_rprprp p q r hp hq hr,
    cyclic_rprprq p q r hp hq hr,
    cyclic_rprqpq p q r hp hq hr,
    cyclic_rprqpr p q r hp hq hr,
    cyclic_rprqrp p q r hp hq hr,
    cyclic_rprqrq p q r hp hq hr,
    cyclic_rqpqpq p q r hp hq hr,
    cyclic_rqpqpr p q r hp hq hr,
    cyclic_rqpqrp p q r hp hq hr,
    cyclic_rqpqrq p q r hp hq hr,
    cyclic_rqprpq p q r hp hq hr,
    cyclic_rqprpr p q r hp hq hr,
    cyclic_rqprqp p q r hp hq hr,
    cyclic_rqprqr p q r hp hq hr,
    cyclic_rqrpqp p q r hp hq hr,
    cyclic_rqrpqr p q r hp hq hr,
    cyclic_rqrprp p q r hp hq hr,
    cyclic_rqrprq p q r hp hq hr,
    cyclic_rqrqpq p q r hp hq hr,
    cyclic_rqrqpr p q r hp hq hr,
    cyclic_rqrqrp p q r hp hq hr,
    cyclic_rqrqrq p q r hp hq hr]
  all_goals ring

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 12000 in
theorem trace_power_7 : Matrix.trace ((p+q+r)^7) =
    (1 : ℂ) * Matrix.trace (p) +
    (42 : ℂ) * Matrix.trace (p*q) +
    (70 : ℂ) * Matrix.trace (p*q*p*q) +
    (14 : ℂ) * Matrix.trace (p*q*p*q*p*q) +
    (7 : ℂ) * Matrix.trace (p*q*p*q*p*q*r) +
    (42 : ℂ) * Matrix.trace (p*q*p*q*p*r) +
    (7 : ℂ) * Matrix.trace (p*q*p*q*p*r*q) +
    (105 : ℂ) * Matrix.trace (p*q*p*q*r) +
    (7 : ℂ) * Matrix.trace (p*q*p*q*r*p*r) +
    (42 : ℂ) * Matrix.trace (p*q*p*q*r*q) +
    (7 : ℂ) * Matrix.trace (p*q*p*q*r*q*r) +
    (140 : ℂ) * Matrix.trace (p*q*p*r) +
    (7 : ℂ) * Matrix.trace (p*q*p*r*p*q*r) +
    (42 : ℂ) * Matrix.trace (p*q*p*r*p*r) +
    (7 : ℂ) * Matrix.trace (p*q*p*r*p*r*q) +
    (105 : ℂ) * Matrix.trace (p*q*p*r*q) +
    (7 : ℂ) * Matrix.trace (p*q*p*r*q*p*r) +
    (42 : ℂ) * Matrix.trace (p*q*p*r*q*r) +
    (7 : ℂ) * Matrix.trace (p*q*p*r*q*r*q) +
    (105 : ℂ) * Matrix.trace (p*q*r) +
    (21 : ℂ) * Matrix.trace (p*q*r*p*q*r) +
    (7 : ℂ) * Matrix.trace (p*q*r*p*q*r*q) +
    (105 : ℂ) * Matrix.trace (p*q*r*p*r) +
    (7 : ℂ) * Matrix.trace (p*q*r*p*r*p*r) +
    (42 : ℂ) * Matrix.trace (p*q*r*p*r*q) +
    (7 : ℂ) * Matrix.trace (p*q*r*p*r*q*r) +
    (140 : ℂ) * Matrix.trace (p*q*r*q) +
    (42 : ℂ) * Matrix.trace (p*q*r*q*p*r) +
    (7 : ℂ) * Matrix.trace (p*q*r*q*p*r*q) +
    (105 : ℂ) * Matrix.trace (p*q*r*q*r) +
    (7 : ℂ) * Matrix.trace (p*q*r*q*r*p*r) +
    (42 : ℂ) * Matrix.trace (p*q*r*q*r*q) +
    (7 : ℂ) * Matrix.trace (p*q*r*q*r*q*r) +
    (42 : ℂ) * Matrix.trace (p*r) +
    (70 : ℂ) * Matrix.trace (p*r*p*r) +
    (14 : ℂ) * Matrix.trace (p*r*p*r*p*r) +
    (7 : ℂ) * Matrix.trace (p*r*p*r*p*r*q) +
    (105 : ℂ) * Matrix.trace (p*r*p*r*q) +
    (42 : ℂ) * Matrix.trace (p*r*p*r*q*r) +
    (7 : ℂ) * Matrix.trace (p*r*p*r*q*r*q) +
    (105 : ℂ) * Matrix.trace (p*r*q) +
    (21 : ℂ) * Matrix.trace (p*r*q*p*r*q) +
    (7 : ℂ) * Matrix.trace (p*r*q*p*r*q*r) +
    (140 : ℂ) * Matrix.trace (p*r*q*r) +
    (105 : ℂ) * Matrix.trace (p*r*q*r*q) +
    (42 : ℂ) * Matrix.trace (p*r*q*r*q*r) +
    (7 : ℂ) * Matrix.trace (p*r*q*r*q*r*q) +
    (1 : ℂ) * Matrix.trace (q) +
    (42 : ℂ) * Matrix.trace (q*r) +
    (70 : ℂ) * Matrix.trace (q*r*q*r) +
    (14 : ℂ) * Matrix.trace (q*r*q*r*q*r) +
    (1 : ℂ) * Matrix.trace (r) := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, add_mul, mul_add, mul_assoc, hp, hq, hr, aux4_idem_tail p _ hp, aux4_idem_tail q _ hq, aux4_idem_tail r _ hr]
  all_goals simp only [← mul_assoc, Matrix.trace_add]
  all_goals simp only [cyclic_qp p q r hp hq hr,
    cyclic_rp p q r hp hq hr,
    cyclic_rq p q r hp hq hr,
    cyclic_pqp p q r hp hq hr,
    cyclic_prp p q r hp hq hr,
    cyclic_qpq p q r hp hq hr,
    cyclic_qpr p q r hp hq hr,
    cyclic_qrp p q r hp hq hr,
    cyclic_qrq p q r hp hq hr,
    cyclic_rpq p q r hp hq hr,
    cyclic_rpr p q r hp hq hr,
    cyclic_rqp p q r hp hq hr,
    cyclic_rqr p q r hp hq hr,
    cyclic_pqrp p q r hp hq hr,
    cyclic_prpq p q r hp hq hr,
    cyclic_prqp p q r hp hq hr,
    cyclic_qpqp p q r hp hq hr,
    cyclic_qpqr p q r hp hq hr,
    cyclic_qprp p q r hp hq hr,
    cyclic_qprq p q r hp hq hr,
    cyclic_qrpq p q r hp hq hr,
    cyclic_qrpr p q r hp hq hr,
    cyclic_qrqp p q r hp hq hr,
    cyclic_rpqp p q r hp hq hr,
    cyclic_rpqr p q r hp hq hr,
    cyclic_rprp p q r hp hq hr,
    cyclic_rprq p q r hp hq hr,
    cyclic_rqpq p q r hp hq hr,
    cyclic_rqpr p q r hp hq hr,
    cyclic_rqrp p q r hp hq hr,
    cyclic_rqrq p q r hp hq hr,
    cyclic_pqpqp p q r hp hq hr,
    cyclic_pqprp p q r hp hq hr,
    cyclic_pqrpq p q r hp hq hr,
    cyclic_pqrqp p q r hp hq hr,
    cyclic_prpqp p q r hp hq hr,
    cyclic_prpqr p q r hp hq hr,
    cyclic_prprp p q r hp hq hr,
    cyclic_prqpq p q r hp hq hr,
    cyclic_prqpr p q r hp hq hr,
    cyclic_prqrp p q r hp hq hr,
    cyclic_qpqpq p q r hp hq hr,
    cyclic_qpqpr p q r hp hq hr,
    cyclic_qpqrp p q r hp hq hr,
    cyclic_qpqrq p q r hp hq hr,
    cyclic_qprpq p q r hp hq hr,
    cyclic_qprpr p q r hp hq hr,
    cyclic_qprqp p q r hp hq hr,
    cyclic_qprqr p q r hp hq hr,
    cyclic_qrpqp p q r hp hq hr,
    cyclic_qrpqr p q r hp hq hr,
    cyclic_qrprp p q r hp hq hr,
    cyclic_qrprq p q r hp hq hr,
    cyclic_qrqpq p q r hp hq hr,
    cyclic_qrqpr p q r hp hq hr,
    cyclic_qrqrp p q r hp hq hr,
    cyclic_qrqrq p q r hp hq hr,
    cyclic_rpqpq p q r hp hq hr,
    cyclic_rpqpr p q r hp hq hr,
    cyclic_rpqrp p q r hp hq hr,
    cyclic_rpqrq p q r hp hq hr,
    cyclic_rprpq p q r hp hq hr,
    cyclic_rprpr p q r hp hq hr,
    cyclic_rprqp p q r hp hq hr,
    cyclic_rprqr p q r hp hq hr,
    cyclic_rqpqp p q r hp hq hr,
    cyclic_rqpqr p q r hp hq hr,
    cyclic_rqprp p q r hp hq hr,
    cyclic_rqprq p q r hp hq hr,
    cyclic_rqrpq p q r hp hq hr,
    cyclic_rqrpr p q r hp hq hr,
    cyclic_rqrqp p q r hp hq hr,
    cyclic_rqrqr p q r hp hq hr,
    cyclic_pqpqrp p q r hp hq hr,
    cyclic_pqprpq p q r hp hq hr,
    cyclic_pqprqp p q r hp hq hr,
    cyclic_pqrpqp p q r hp hq hr,
    cyclic_pqrprp p q r hp hq hr,
    cyclic_pqrqpq p q r hp hq hr,
    cyclic_pqrqrp p q r hp hq hr,
    cyclic_prpqpq p q r hp hq hr,
    cyclic_prpqpr p q r hp hq hr,
    cyclic_prpqrp p q r hp hq hr,
    cyclic_prpqrq p q r hp hq hr,
    cyclic_prprpq p q r hp hq hr,
    cyclic_prprqp p q r hp hq hr,
    cyclic_prqpqp p q r hp hq hr,
    cyclic_prqpqr p q r hp hq hr,
    cyclic_prqprp p q r hp hq hr,
    cyclic_prqrpq p q r hp hq hr,
    cyclic_prqrpr p q r hp hq hr,
    cyclic_prqrqp p q r hp hq hr,
    cyclic_qpqpqp p q r hp hq hr,
    cyclic_qpqpqr p q r hp hq hr,
    cyclic_qpqprp p q r hp hq hr,
    cyclic_qpqprq p q r hp hq hr,
    cyclic_qpqrpq p q r hp hq hr,
    cyclic_qpqrpr p q r hp hq hr,
    cyclic_qpqrqp p q r hp hq hr,
    cyclic_qpqrqr p q r hp hq hr,
    cyclic_qprpqp p q r hp hq hr,
    cyclic_qprpqr p q r hp hq hr,
    cyclic_qprprp p q r hp hq hr,
    cyclic_qprprq p q r hp hq hr,
    cyclic_qprqpq p q r hp hq hr,
    cyclic_qprqpr p q r hp hq hr,
    cyclic_qprqrp p q r hp hq hr,
    cyclic_qprqrq p q r hp hq hr,
    cyclic_qrpqpq p q r hp hq hr,
    cyclic_qrpqpr p q r hp hq hr,
    cyclic_qrpqrp p q r hp hq hr,
    cyclic_qrpqrq p q r hp hq hr,
    cyclic_qrprpq p q r hp hq hr,
    cyclic_qrprpr p q r hp hq hr,
    cyclic_qrprqp p q r hp hq hr,
    cyclic_qrprqr p q r hp hq hr,
    cyclic_qrqpqp p q r hp hq hr,
    cyclic_qrqpqr p q r hp hq hr,
    cyclic_qrqprp p q r hp hq hr,
    cyclic_qrqprq p q r hp hq hr,
    cyclic_qrqrpq p q r hp hq hr,
    cyclic_qrqrpr p q r hp hq hr,
    cyclic_qrqrqp p q r hp hq hr,
    cyclic_rpqpqp p q r hp hq hr,
    cyclic_rpqpqr p q r hp hq hr,
    cyclic_rpqprp p q r hp hq hr,
    cyclic_rpqprq p q r hp hq hr,
    cyclic_rpqrpq p q r hp hq hr,
    cyclic_rpqrpr p q r hp hq hr,
    cyclic_rpqrqp p q r hp hq hr,
    cyclic_rpqrqr p q r hp hq hr,
    cyclic_rprpqp p q r hp hq hr,
    cyclic_rprpqr p q r hp hq hr,
    cyclic_rprprp p q r hp hq hr,
    cyclic_rprprq p q r hp hq hr,
    cyclic_rprqpq p q r hp hq hr,
    cyclic_rprqpr p q r hp hq hr,
    cyclic_rprqrp p q r hp hq hr,
    cyclic_rprqrq p q r hp hq hr,
    cyclic_rqpqpq p q r hp hq hr,
    cyclic_rqpqpr p q r hp hq hr,
    cyclic_rqpqrp p q r hp hq hr,
    cyclic_rqpqrq p q r hp hq hr,
    cyclic_rqprpq p q r hp hq hr,
    cyclic_rqprpr p q r hp hq hr,
    cyclic_rqprqp p q r hp hq hr,
    cyclic_rqprqr p q r hp hq hr,
    cyclic_rqrpqp p q r hp hq hr,
    cyclic_rqrpqr p q r hp hq hr,
    cyclic_rqrprp p q r hp hq hr,
    cyclic_rqrprq p q r hp hq hr,
    cyclic_rqrqpq p q r hp hq hr,
    cyclic_rqrqpr p q r hp hq hr,
    cyclic_rqrqrp p q r hp hq hr,
    cyclic_rqrqrq p q r hp hq hr,
    cyclic_pqpqpqp p q r hp hq hr,
    cyclic_pqpqprp p q r hp hq hr,
    cyclic_pqpqrpq p q r hp hq hr,
    cyclic_pqpqrqp p q r hp hq hr,
    cyclic_pqprpqp p q r hp hq hr,
    cyclic_pqprprp p q r hp hq hr,
    cyclic_pqprqpq p q r hp hq hr,
    cyclic_pqprqrp p q r hp hq hr,
    cyclic_pqrpqpq p q r hp hq hr,
    cyclic_pqrpqpr p q r hp hq hr,
    cyclic_pqrpqrp p q r hp hq hr,
    cyclic_pqrprpq p q r hp hq hr,
    cyclic_pqrprqp p q r hp hq hr,
    cyclic_pqrqpqp p q r hp hq hr,
    cyclic_pqrqpqr p q r hp hq hr,
    cyclic_pqrqprp p q r hp hq hr,
    cyclic_pqrqrpq p q r hp hq hr,
    cyclic_pqrqrqp p q r hp hq hr,
    cyclic_prpqpqp p q r hp hq hr,
    cyclic_prpqpqr p q r hp hq hr,
    cyclic_prpqprp p q r hp hq hr,
    cyclic_prpqprq p q r hp hq hr,
    cyclic_prpqrpq p q r hp hq hr,
    cyclic_prpqrpr p q r hp hq hr,
    cyclic_prpqrqp p q r hp hq hr,
    cyclic_prpqrqr p q r hp hq hr,
    cyclic_prprpqp p q r hp hq hr,
    cyclic_prprpqr p q r hp hq hr,
    cyclic_prprprp p q r hp hq hr,
    cyclic_prprqpq p q r hp hq hr,
    cyclic_prprqpr p q r hp hq hr,
    cyclic_prprqrp p q r hp hq hr,
    cyclic_prqpqpq p q r hp hq hr,
    cyclic_prqpqpr p q r hp hq hr,
    cyclic_prqpqrp p q r hp hq hr,
    cyclic_prqpqrq p q r hp hq hr,
    cyclic_prqprpq p q r hp hq hr,
    cyclic_prqprpr p q r hp hq hr,
    cyclic_prqprqp p q r hp hq hr,
    cyclic_prqrpqp p q r hp hq hr,
    cyclic_prqrpqr p q r hp hq hr,
    cyclic_prqrprp p q r hp hq hr,
    cyclic_prqrprq p q r hp hq hr,
    cyclic_prqrqpq p q r hp hq hr,
    cyclic_prqrqpr p q r hp hq hr,
    cyclic_prqrqrp p q r hp hq hr,
    cyclic_qpqpqpq p q r hp hq hr,
    cyclic_qpqpqpr p q r hp hq hr,
    cyclic_qpqpqrp p q r hp hq hr,
    cyclic_qpqpqrq p q r hp hq hr,
    cyclic_qpqprpq p q r hp hq hr,
    cyclic_qpqprpr p q r hp hq hr,
    cyclic_qpqprqp p q r hp hq hr,
    cyclic_qpqprqr p q r hp hq hr,
    cyclic_qpqrpqp p q r hp hq hr,
    cyclic_qpqrpqr p q r hp hq hr,
    cyclic_qpqrprp p q r hp hq hr,
    cyclic_qpqrprq p q r hp hq hr,
    cyclic_qpqrqpq p q r hp hq hr,
    cyclic_qpqrqpr p q r hp hq hr,
    cyclic_qpqrqrp p q r hp hq hr,
    cyclic_qpqrqrq p q r hp hq hr,
    cyclic_qprpqpq p q r hp hq hr,
    cyclic_qprpqpr p q r hp hq hr,
    cyclic_qprpqrp p q r hp hq hr,
    cyclic_qprpqrq p q r hp hq hr,
    cyclic_qprprpq p q r hp hq hr,
    cyclic_qprprpr p q r hp hq hr,
    cyclic_qprprqp p q r hp hq hr,
    cyclic_qprprqr p q r hp hq hr,
    cyclic_qprqpqp p q r hp hq hr,
    cyclic_qprqpqr p q r hp hq hr,
    cyclic_qprqprp p q r hp hq hr,
    cyclic_qprqprq p q r hp hq hr,
    cyclic_qprqrpq p q r hp hq hr,
    cyclic_qprqrpr p q r hp hq hr,
    cyclic_qprqrqp p q r hp hq hr,
    cyclic_qprqrqr p q r hp hq hr,
    cyclic_qrpqpqp p q r hp hq hr,
    cyclic_qrpqpqr p q r hp hq hr,
    cyclic_qrpqprp p q r hp hq hr,
    cyclic_qrpqprq p q r hp hq hr,
    cyclic_qrpqrpq p q r hp hq hr,
    cyclic_qrpqrpr p q r hp hq hr,
    cyclic_qrpqrqp p q r hp hq hr,
    cyclic_qrpqrqr p q r hp hq hr,
    cyclic_qrprpqp p q r hp hq hr,
    cyclic_qrprpqr p q r hp hq hr,
    cyclic_qrprprp p q r hp hq hr,
    cyclic_qrprprq p q r hp hq hr,
    cyclic_qrprqpq p q r hp hq hr,
    cyclic_qrprqpr p q r hp hq hr,
    cyclic_qrprqrp p q r hp hq hr,
    cyclic_qrprqrq p q r hp hq hr,
    cyclic_qrqpqpq p q r hp hq hr,
    cyclic_qrqpqpr p q r hp hq hr,
    cyclic_qrqpqrp p q r hp hq hr,
    cyclic_qrqpqrq p q r hp hq hr,
    cyclic_qrqprpq p q r hp hq hr,
    cyclic_qrqprpr p q r hp hq hr,
    cyclic_qrqprqp p q r hp hq hr,
    cyclic_qrqprqr p q r hp hq hr,
    cyclic_qrqrpqp p q r hp hq hr,
    cyclic_qrqrpqr p q r hp hq hr,
    cyclic_qrqrprp p q r hp hq hr,
    cyclic_qrqrprq p q r hp hq hr,
    cyclic_qrqrqpq p q r hp hq hr,
    cyclic_qrqrqpr p q r hp hq hr,
    cyclic_qrqrqrp p q r hp hq hr,
    cyclic_qrqrqrq p q r hp hq hr,
    cyclic_rpqpqpq p q r hp hq hr,
    cyclic_rpqpqpr p q r hp hq hr,
    cyclic_rpqpqrp p q r hp hq hr,
    cyclic_rpqpqrq p q r hp hq hr,
    cyclic_rpqprpq p q r hp hq hr,
    cyclic_rpqprpr p q r hp hq hr,
    cyclic_rpqprqp p q r hp hq hr,
    cyclic_rpqprqr p q r hp hq hr,
    cyclic_rpqrpqp p q r hp hq hr,
    cyclic_rpqrpqr p q r hp hq hr,
    cyclic_rpqrprp p q r hp hq hr,
    cyclic_rpqrprq p q r hp hq hr,
    cyclic_rpqrqpq p q r hp hq hr,
    cyclic_rpqrqpr p q r hp hq hr,
    cyclic_rpqrqrp p q r hp hq hr,
    cyclic_rpqrqrq p q r hp hq hr,
    cyclic_rprpqpq p q r hp hq hr,
    cyclic_rprpqpr p q r hp hq hr,
    cyclic_rprpqrp p q r hp hq hr,
    cyclic_rprpqrq p q r hp hq hr,
    cyclic_rprprpq p q r hp hq hr,
    cyclic_rprprpr p q r hp hq hr,
    cyclic_rprprqp p q r hp hq hr,
    cyclic_rprprqr p q r hp hq hr,
    cyclic_rprqpqp p q r hp hq hr,
    cyclic_rprqpqr p q r hp hq hr,
    cyclic_rprqprp p q r hp hq hr,
    cyclic_rprqprq p q r hp hq hr,
    cyclic_rprqrpq p q r hp hq hr,
    cyclic_rprqrpr p q r hp hq hr,
    cyclic_rprqrqp p q r hp hq hr,
    cyclic_rprqrqr p q r hp hq hr,
    cyclic_rqpqpqp p q r hp hq hr,
    cyclic_rqpqpqr p q r hp hq hr,
    cyclic_rqpqprp p q r hp hq hr,
    cyclic_rqpqprq p q r hp hq hr,
    cyclic_rqpqrpq p q r hp hq hr,
    cyclic_rqpqrpr p q r hp hq hr,
    cyclic_rqpqrqp p q r hp hq hr,
    cyclic_rqpqrqr p q r hp hq hr,
    cyclic_rqprpqp p q r hp hq hr,
    cyclic_rqprpqr p q r hp hq hr,
    cyclic_rqprprp p q r hp hq hr,
    cyclic_rqprprq p q r hp hq hr,
    cyclic_rqprqpq p q r hp hq hr,
    cyclic_rqprqpr p q r hp hq hr,
    cyclic_rqprqrp p q r hp hq hr,
    cyclic_rqprqrq p q r hp hq hr,
    cyclic_rqrpqpq p q r hp hq hr,
    cyclic_rqrpqpr p q r hp hq hr,
    cyclic_rqrpqrp p q r hp hq hr,
    cyclic_rqrpqrq p q r hp hq hr,
    cyclic_rqrprpq p q r hp hq hr,
    cyclic_rqrprpr p q r hp hq hr,
    cyclic_rqrprqp p q r hp hq hr,
    cyclic_rqrprqr p q r hp hq hr,
    cyclic_rqrqpqp p q r hp hq hr,
    cyclic_rqrqpqr p q r hp hq hr,
    cyclic_rqrqprp p q r hp hq hr,
    cyclic_rqrqprq p q r hp hq hr,
    cyclic_rqrqrpq p q r hp hq hr,
    cyclic_rqrqrpr p q r hp hq hr,
    cyclic_rqrqrqp p q r hp hq hr,
    cyclic_rqrqrqr p q r hp hq hr]
  all_goals ring
end FourMeasWords
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral

private theorem aux5_left_tail {D : ℕ} (p m x : Mat D) (h : p*m=m) : p*(m*x)=m*x := by
  rw [← mul_assoc,h]
private theorem aux6_right_tail {D : ℕ} (p m x : Mat D) (h : m*p=m) : m*(p*x)=m*x := by
  rw [← mul_assoc,h]

theorem supported_centered_cube {D : ℕ} (p m : Mat D) (u : ℝ)
    (hp : p*p=p) (hpm : p*m=m) (hmp : m*p=m) :
    (m-u•p)^3 = m^3 - (3*u)•(m^2) + (3*u^2)•m - (u^3)•p := by
  simp only [pow_succ, pow_zero, mul_one, one_mul, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, smul_smul, mul_assoc, hp,hpm,hmp,
    aux5_left_tail p m _ hpm, aux6_right_tail p m _ hmp, aux5_left_tail p p _ hp]
  module

theorem pairKappa_point {n D : ℕ} (P Q : PVM n D) (a b : Fin n) :
    matTrace ((pairDefect P Q a b)^3) =
      matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b) -
        (3*(n:ℝ)⁻¹)*matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b) +
        (3*((n:ℝ)⁻¹)^2)*matTrace (P.proj a*Q.proj b) -
        ((n:ℝ)⁻¹)^3*matTrace (P.proj a) := by
  let p := P.proj a
  let q := Q.proj b
  have hp : p*p=p := (P.isProj a).isIdempotentElem.eq
  have hq : q*q=q := (Q.isProj b).isIdempotentElem.eq
  have hl : p*(p*q*p)=p*q*p := by simp only [←mul_assoc,hp]
  have hr : (p*q*p)*p=p*q*p := by simp only [mul_assoc,hp]
  have t1 := PairTraceIdentities.sandwich_trace p q hp
  have t2 : Matrix.trace ((p*q*p)^2) = Matrix.trace (p*q*p*q) := by
    simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc,aux5_left_tail p p _ hp]
    simpa only [mul_assoc] using FourMeasWords.cyclic_pqpqp p q p hp hq hp
  have t3 : Matrix.trace ((p*q*p)^3) = Matrix.trace (p*q*p*q*p*q) := by
    simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc,aux5_left_tail p p _ hp]
    simpa only [mul_assoc] using FourMeasWords.cyclic_pqpqpqp p q p hp hq hp
  change matTrace (((p*q*p)-(n:ℝ)⁻¹•p)^3) = _
  rw [supported_centered_cube p (p*q*p) (n:ℝ)⁻¹ hp hl hr]
  simp only [matTrace, Matrix.trace_sub,Matrix.trace_add,Matrix.trace_smul,t1,t2,t3,
    Complex.sub_re,Complex.add_re,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero]
  rfl

theorem pair_cubic_alternating {n D : ℕ} (hn : 0<n) (P Q : PVM n D) :
    (∑ a,∑ b,matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)) =
      (D:ℝ)/(n:ℝ)^2 + (3/(n:ℝ))*pairSigma P Q + pairKappa P Q := by
  have hk : pairKappa P Q =
      (∑ a,∑ b,matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)) -
        (3*(n:ℝ)⁻¹)*(∑ a,∑ b,matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b)) +
        (3*((n:ℝ)⁻¹)^2)*(D:ℝ) - ((n:ℝ)⁻¹)^3*((n:ℝ)*D) := by
    unfold pairKappa
    simp_rw [pairKappa_point]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum]
    rw [(PairTraceIdentities.pair_trace_totals P Q).1]
    have hr := (PairTraceIdentities.pair_trace_totals P Q).2
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      ←Finset.mul_sum] at hr ⊢
    rw [hr]
  rw [pairSigma_eq_alternating hn, hk]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}

theorem pairKappa_symm (P Q : PVM n D) : pairKappa P Q = pairKappa Q P := by
  by_cases hn : n=0
  · subst n
    simp only [pairKappa, Finset.univ_eq_empty, Finset.sum_empty]
  have hnpos : 0<n := Nat.pos_of_ne_zero hn
  have hp := pair_cubic_alternating hnpos P Q
  have hq := pair_cubic_alternating hnpos Q P
  have ht : (∑ a, ∑ b, matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)) =
      ∑ b, ∑ a, matTrace (Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro a _
    unfold matTrace
    apply congrArg Complex.re
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a)
      (Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)
  rw [pairSigma_symm P Q] at hp
  linarith

theorem sum3_pair_four (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b (_ : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b)) =
      (n:ℝ)*((D:ℝ)/(n:ℝ)+pairSigma P Q) := by
  have h := pairSigma_eq_alternating hn P Q
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  apply congrArg ((n:ℝ) * ·)
  linarith

theorem sum3_pair_six (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b (_ : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)) =
      (n:ℝ)*((D:ℝ)/(n:ℝ)^2+(3/(n:ℝ))*pairSigma P Q+pairKappa P Q) := by
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [pair_cubic_alternating hn P Q]

theorem total_pair_four (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b (_:Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b)) +
    sum3 (fun a (_:Fin n) c => matTrace (P.proj a*R.proj c*P.proj a*R.proj c)) +
    sum3 (fun (_:Fin n) b c => matTrace (Q.proj b*R.proj c*Q.proj b*R.proj c)) =
      (n:ℝ)*totalSigma P Q R+3*(D:ℝ) := by
  have hpr := sum3_pair_four hn P R Q
  rw [← sum3_acb (fun a b (_:Fin n) => matTrace (P.proj a*R.proj b*P.proj a*R.proj b))] at hpr
  have hqr := sum3_pair_four hn Q R P
  rw [← sum3_bca (fun a b (_:Fin n) => matTrace (Q.proj a*R.proj b*Q.proj a*R.proj b))] at hqr
  rw [sum3_pair_four hn P Q R, hpr, hqr]
  unfold totalSigma
  rw [pairSigma_symm R P]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

theorem total_pair_six (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b (_:Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*P.proj a*Q.proj b)) +
    sum3 (fun a (_:Fin n) c => matTrace (P.proj a*R.proj c*P.proj a*R.proj c*P.proj a*R.proj c)) +
    sum3 (fun (_:Fin n) b c => matTrace (Q.proj b*R.proj c*Q.proj b*R.proj c*Q.proj b*R.proj c)) =
      (n:ℝ)*totalKappa P Q R+3*totalSigma P Q R+3*(D:ℝ)/(n:ℝ) := by
  have hpr := sum3_pair_six hn P R Q
  rw [← sum3_acb (fun a b (_:Fin n) => matTrace (P.proj a*R.proj b*P.proj a*R.proj b*P.proj a*R.proj b))] at hpr
  have hqr := sum3_pair_six hn Q R P
  rw [← sum3_bca (fun a b (_:Fin n) => matTrace (Q.proj a*R.proj b*Q.proj a*R.proj b*Q.proj a*R.proj b))] at hqr
  rw [sum3_pair_six hn P Q R, hpr, hqr]
  unfold totalSigma totalKappa
  rw [pairSigma_symm R P, pairKappa_symm R P]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments

theorem sum3_trace_singleton {n D : ℕ} (hn : 0 < n) (P : PVM n D)
    (F : Fin n → Fin n → Mat D) :
    sum3 (fun a b c => Matrix.trace (P.proj a * F b c)) =
      (n : ℂ)⁻¹ * sum3 (fun (_ : Fin n) b c => Matrix.trace (F b c)) := by
  have hx : sum3 (fun a b c => Matrix.trace (P.proj a * F b c)) =
      ∑ b, ∑ c, Matrix.trace (F b c) := by
    unfold sum3
    calc
      _ = ∑ b, ∑ a, ∑ c, Matrix.trace (P.proj a * F b c) := Finset.sum_comm
      _ = ∑ b, ∑ c, ∑ a, Matrix.trace (P.proj a * F b c) := by
        apply Finset.sum_congr rfl
        intro b _
        exact Finset.sum_comm
      _ = _ := by
        simp only [← Matrix.trace_sum, ← Finset.sum_mul, P.complete, one_mul]
  rw [hx]
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp

theorem sum3_trace_one {n D : ℕ} :
    sum3 (fun (_ _ _ : Fin n) => Matrix.trace (1 : Mat D)) = (n : ℂ)^3 * D := by
  simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Matrix.trace_one]
  ring

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
private theorem aux7_idem_tail {D : ℕ} (a b : Mat D) (h : a*a=a) : a*(a*b)=a*b := by
  rw [← mul_assoc,h]
variable {n D : ℕ} (hn : 0<n) (P Q R : PVM n D)
include hn P Q R

theorem delete_p : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace ((1 : Mat D)))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a) = Matrix.trace (P.proj a * ((1 : Mat D))) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => (1 : Mat D))
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_q : sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace ((1 : Mat D)))) := by
  have ht (a b c : Fin n) : Matrix.trace (Q.proj b) = Matrix.trace (Q.proj b * ((1 : Mat D))) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => (1 : Mat D))
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * ((1 : Mat D)))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace ((1 : Mat D)))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_r : sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace ((1 : Mat D)))) := by
  have ht (a b c : Fin n) : Matrix.trace (R.proj c) = Matrix.trace (R.proj c * ((1 : Mat D))) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => (1 : Mat D))
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * ((1 : Mat D)))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace ((1 : Mat D)))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_pq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b) = Matrix.trace (P.proj a * (Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_pr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c) = Matrix.trace (P.proj a * (R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c)
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_qr : sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (Q.proj b * R.proj c) = Matrix.trace (Q.proj b * (R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => R.proj c)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (R.proj c))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (R.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_pqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c) = Matrix.trace (P.proj a * (Q.proj b * R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b * R.proj c)
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_prq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * Q.proj b) = Matrix.trace (P.proj a * (R.proj c * Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c * Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * Q.proj b) = Matrix.trace (Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqpr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c) = Matrix.trace (Q.proj b * (P.proj a * R.proj c * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a) (Q.proj b * P.proj a * R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => P.proj b * R.proj c * P.proj b)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (P.proj b * R.proj c * P.proj b))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (P.proj b * R.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * P.proj a) = Matrix.trace (P.proj a * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_prp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (P.proj a * (Q.proj b * R.proj c * Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b * R.proj c * Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (Q.proj b * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_qrq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_prqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c) = Matrix.trace (P.proj a * (R.proj c * Q.proj b * R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c * Q.proj b * R.proj c)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * Q.proj b * R.proj c) = Matrix.trace (Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rqr (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqpqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c) = Matrix.trace (R.proj c * (P.proj a * Q.proj b * P.proj a * Q.proj b)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a * Q.proj b) (R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => P.proj b * Q.proj c * P.proj b * Q.proj c)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (P.proj b * Q.proj c * P.proj b * Q.proj c))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (P.proj b * Q.proj c * P.proj b * Q.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_pqprq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b) = Matrix.trace (R.proj c * (Q.proj b * P.proj a * Q.proj b * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a) (R.proj c * Q.proj b)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => Q.proj c * P.proj b * Q.proj c * P.proj b)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (Q.proj c * P.proj b * Q.proj c * P.proj b))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (Q.proj c * P.proj b * Q.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (Q.proj b * P.proj a * Q.proj b * P.proj a) = Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_qpqp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrpr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c) = Matrix.trace (Q.proj b * (R.proj c * P.proj a * R.proj c * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a) (Q.proj b * R.proj c * P.proj a * R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => R.proj c * P.proj b * R.proj c * P.proj b)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (R.proj c * P.proj b * R.proj c * P.proj b))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (R.proj c * P.proj b * R.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * P.proj a * R.proj c * P.proj a) = Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rprp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c) = Matrix.trace (P.proj a * (Q.proj b * R.proj c * Q.proj b * R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b * R.proj c * Q.proj b * R.proj c)
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_prprq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * (P.proj a * R.proj c * P.proj a * R.proj c)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * R.proj c * P.proj a * R.proj c) (Q.proj b)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => P.proj b * R.proj c * P.proj b * R.proj c)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (P.proj b * R.proj c * P.proj b * R.proj c))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (P.proj b * R.proj c * P.proj b * R.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_prqrq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (P.proj a * (R.proj c * Q.proj b * R.proj c * Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c * Q.proj b * R.proj c * Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rqrq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqpqpr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c) = Matrix.trace (R.proj c * (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a) (R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a) = Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_pqpqp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqpqrq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (R.proj c * (Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a * Q.proj b) (R.proj c * Q.proj b)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b) = Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_qpqpq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqprpr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c) = Matrix.trace (Q.proj b * (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a) (Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => P.proj b * R.proj c * P.proj b * R.proj c * P.proj b)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (P.proj b * R.proj c * P.proj b * R.proj c * P.proj b))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (P.proj b * R.proj c * P.proj b * R.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a) = Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_prprp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrqrq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (P.proj a * (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_qrqrq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_prprqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c) = Matrix.trace (Q.proj b * (R.proj c * P.proj a * R.proj c * P.proj a * R.proj c)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * R.proj c * P.proj a * R.proj c) (Q.proj b * R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => R.proj c * P.proj b * R.proj c * P.proj b * R.proj c)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (R.proj c * P.proj b * R.proj c * P.proj b * R.proj c))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (R.proj c * P.proj b * R.proj c * P.proj b * R.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * P.proj a * R.proj c * P.proj a * R.proj c) = Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rprpr (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_prqrqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c) = Matrix.trace (P.proj a * (R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c) = Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rqrqr (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqpqpqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c) = Matrix.trace (R.proj c * (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b) (R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_pqpqprq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b) = Matrix.trace (R.proj c * (Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a) (R.proj c * Q.proj b)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn R (fun b c => Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b)
  rw [← sum3_cab (fun a b c => Matrix.trace (R.proj a * (Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b))),
    ← sum3_cab (fun (a b c : Fin n) => Matrix.trace (Q.proj c * P.proj b * Q.proj c * P.proj b * Q.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a) = Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_qpqpqp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrprpr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c) = Matrix.trace (Q.proj b * (R.proj c * P.proj a * R.proj c * P.proj a * R.proj c * P.proj a)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a) (Q.proj b * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => R.proj c * P.proj b * R.proj c * P.proj b * R.proj c * P.proj b)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (R.proj c * P.proj b * R.proj c * P.proj b * R.proj c * P.proj b))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (R.proj c * P.proj b * R.proj c * P.proj b * R.proj c * P.proj b))] at h
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * P.proj a * R.proj c * P.proj a * R.proj c * P.proj a) = Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rprprp (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
theorem delete_pqrqrqr : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c) = Matrix.trace (P.proj a * (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c)
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_prprprq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c)) := by
    simpa only [mul_assoc] using Matrix.trace_mul_comm (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c) (Q.proj b)
  try simp_rw [ht]
  have h := sum3_trace_singleton hn Q (fun b c => P.proj b * R.proj c * P.proj b * R.proj c * P.proj b * R.proj c)
  rw [← sum3_bac (fun a b c => Matrix.trace (Q.proj a * (P.proj b * R.proj c * P.proj b * R.proj c * P.proj b * R.proj c))),
    ← sum3_bac (fun (a b c : Fin n) => Matrix.trace (P.proj b * R.proj c * P.proj b * R.proj c * P.proj b * R.proj c))] at h
  try simp only [mul_one] at h
  rw [h]
  all_goals rfl
theorem delete_prqrqrq : sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)) = (n:ℂ)⁻¹ * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have ht (a b c : Fin n) : Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (P.proj a * (R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)) := by
    simp only [mul_assoc, mul_one]
  try simp_rw [ht]
  have h := sum3_trace_singleton hn P (fun b c => R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b)
  try simp only [mul_one] at h
  rw [h]
  have hc (a b c : Fin n) : Matrix.trace (R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b) = Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c) := by
    try simp only [mul_assoc, (P.isProj a).isIdempotentElem.eq, (Q.isProj b).isIdempotentElem.eq, (R.isProj c).isIdempotentElem.eq,
      aux7_idem_tail (P.proj a) _ (P.isProj a).isIdempotentElem.eq, aux7_idem_tail (Q.proj b) _ (Q.isProj b).isIdempotentElem.eq, aux7_idem_tail (R.proj c) _ (R.isProj c).isIdempotentElem.eq]
    all_goals try simp only [← mul_assoc]
    all_goals exact FourMeasWords.cyclic_rqrqrq (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  apply congrArg ((n:ℂ)⁻¹ * ·)
  apply congrArg sum3
  funext a b c
  exact hc a b c
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
set_option maxHeartbeats 6000000
variable {n D : ℕ} (hn : 0<n) (P Q R : PVM n D)
include hn P Q R
theorem raw_trace_moment_1 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^1)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1) * ((n:ℂ)^3 * (D:ℂ)) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_1 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_2 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^2)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (6:ℂ)*(n:ℂ)⁻¹^2) * ((n:ℂ)^3 * (D:ℂ)) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_2 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_3 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^3)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (18:ℂ)*(n:ℂ)⁻¹^2 + (6:ℂ)*(n:ℂ)⁻¹^3) * ((n:ℂ)^3 * (D:ℂ)) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_3 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (3:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (3:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_4 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^4)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (36:ℂ)*(n:ℂ)⁻¹^2 + (36:ℂ)*(n:ℂ)⁻¹^3) * ((n:ℂ)^3 * (D:ℂ)) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_4 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (12:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (4:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (12:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c))) +
        (4:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (12:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
        (12:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b))) +
        (4:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (12:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_5 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^5)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (60:ℂ)*(n:ℂ)⁻¹^2 + (120:ℂ)*(n:ℂ)⁻¹^3) * ((n:ℂ)^3 * (D:ℂ)) +
    ((10:ℂ) + (10:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((10:ℂ) + (10:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((10:ℂ) + (10:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_5 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (10:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (10:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (5:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (20:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (10:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_6 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^6)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (90:ℂ)*(n:ℂ)⁻¹^2 + (300:ℂ)*(n:ℂ)⁻¹^3) * ((n:ℂ)^3 * (D:ℂ)) +
    ((30:ℂ) + (72:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((6:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((3:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((6:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((6:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((30:ℂ) + (72:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((3:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((30:ℂ) + (72:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((2:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_6 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (60:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (60:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c))) +
        (3:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (60:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (60:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b))) +
        (3:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (60:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (6:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (30:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (2:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
theorem raw_trace_moment_7 : sum3 (fun a b c => Matrix.trace ((P.proj a+Q.proj b+R.proj c)^7)) =
    ((3:ℂ)*(n:ℂ)⁻¹^1 + (126:ℂ)*(n:ℂ)⁻¹^2 + (630:ℂ)*(n:ℂ)⁻¹^3) * ((n:ℂ)^3 * (D:ℂ)) +
    ((70:ℂ) + (294:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((14:ℂ) + (14:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((42:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
    ((21:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c * Q.proj b))) +
    ((42:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((42:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * P.proj a * R.proj c))) +
    ((70:ℂ) + (294:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((14:ℂ) + (14:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
    ((21:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℂ)) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((70:ℂ) + (294:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((14:ℂ) + (14:ℂ)*(n:ℂ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have hp (a b c : Fin n) := FourMeasWords.trace_power_7 (P.proj a) (Q.proj b) (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
  calc
    _ = (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b))) +
        (70:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (14:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (140:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * Q.proj b * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c))) +
        (21:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (140:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * P.proj a * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c))) +
        (70:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c))) +
        (14:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b))) +
        (21:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (140:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c))) +
        (105:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (7:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b))) +
        (42:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c))) +
        (70:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (14:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
        (1:ℂ) * (sum3 (fun (a b c : Fin n) => Matrix.trace (R.proj c))) := by simp (config := { maxSteps := 200000 }) only [sum3, hp, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      simp only [delete_p hn P Q R, delete_q hn P Q R, delete_r hn P Q R, delete_pq hn P Q R, delete_pr hn P Q R, delete_qr hn P Q R, delete_pqr hn P Q R, delete_prq hn P Q R, delete_pqpr hn P Q R, delete_pqrq hn P Q R, delete_prqr hn P Q R, delete_pqpqr hn P Q R, delete_pqprq hn P Q R, delete_pqrpr hn P Q R, delete_pqrqr hn P Q R, delete_prprq hn P Q R, delete_prqrq hn P Q R, delete_pqpqpr hn P Q R, delete_pqpqrq hn P Q R, delete_pqprpr hn P Q R, delete_pqrqrq hn P Q R, delete_prprqr hn P Q R, delete_prqrqr hn P Q R, delete_pqpqpqr hn P Q R, delete_pqpqprq hn P Q R, delete_pqrprpr hn P Q R, delete_pqrqrqr hn P Q R, delete_prprprq hn P Q R, delete_prqrqrq hn P Q R, sum3_trace_one]
      ring
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ} (hn:0<n) (P Q R:PVM n D)
include hn P Q R
theorem real_raw_trace_moment_4 : sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^4)) =
    ((3:ℝ)*(n:ℝ)⁻¹^1 + (36:ℝ)*(n:ℝ)⁻¹^2 + (36:ℝ)*(n:ℝ)⁻¹^3) * ((n:ℝ)^3 * (D:ℝ)) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have h := congrArg Complex.re (raw_trace_moment_4 hn P Q R)
  simpa only [sum3, Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, matTrace] using h
theorem real_raw_trace_moment_5 : sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^5)) =
    ((3:ℝ)*(n:ℝ)⁻¹^1 + (60:ℝ)*(n:ℝ)⁻¹^2 + (120:ℝ)*(n:ℝ)⁻¹^3) * ((n:ℝ)^3 * (D:ℝ)) +
    ((10:ℝ) + (10:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((10:ℝ) + (10:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((10:ℝ) + (10:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have h := congrArg Complex.re (raw_trace_moment_5 hn P Q R)
  simpa only [sum3, Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, matTrace] using h
theorem real_raw_trace_moment_6 : sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^6)) =
    ((3:ℝ)*(n:ℝ)⁻¹^1 + (90:ℝ)*(n:ℝ)⁻¹^2 + (300:ℝ)*(n:ℝ)⁻¹^3) * ((n:ℝ)^3 * (D:ℝ)) +
    ((30:ℝ) + (72:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((6:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((3:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((6:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((6:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((30:ℝ) + (72:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((3:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((30:ℝ) + (72:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((2:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have h := congrArg Complex.re (raw_trace_moment_6 hn P Q R)
  simpa only [sum3, Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, matTrace] using h
theorem real_raw_trace_moment_7 : sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^7)) =
    ((3:ℝ)*(n:ℝ)⁻¹^1 + (126:ℝ)*(n:ℝ)⁻¹^2 + (630:ℝ)*(n:ℝ)⁻¹^3) * ((n:ℝ)^3 * (D:ℝ)) +
    ((70:ℝ) + (294:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((14:ℝ) + (14:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b * P.proj a * Q.proj b))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((42:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
    ((21:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c * Q.proj b))) +
    ((42:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((42:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * Q.proj b * R.proj c * Q.proj b * R.proj c * P.proj a * R.proj c))) +
    ((70:ℝ) + (294:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((14:ℝ) + (14:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c * P.proj a * R.proj c))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * P.proj a * R.proj c * Q.proj b * R.proj c * Q.proj b))) +
    ((21:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b))) +
    ((7:ℝ)) * (sum3 (fun (a b c : Fin n) => matTrace (P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b * R.proj c))) +
    ((70:ℝ) + (294:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c))) +
    ((14:ℝ) + (14:ℝ)*(n:ℝ)⁻¹^1) * (sum3 (fun (a b c : Fin n) => matTrace (Q.proj b * R.proj c * Q.proj b * R.proj c * Q.proj b * R.proj c))) := by
  have h := congrArg Complex.re (raw_trace_moment_7 hn P Q R)
  simpa only [sum3, Complex.re_sum, ← Complex.ofReal_natCast, ← Complex.ofReal_ofNat,
    ← Complex.ofReal_inv, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    Complex.ofReal_re, Complex.add_re, Complex.re_ofReal_mul, matTrace] using h
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}

theorem raw_four (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^4)) =
      (3*(n:ℝ)^2+36*(n:ℝ)+42)*(D:ℝ)+2*(n:ℝ)*totalSigma P Q R := by
  have hpair := total_pair_four hn P Q R
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    _ = (3*(n:ℝ)⁻¹+36*((n:ℝ)⁻¹)^2+36*((n:ℝ)⁻¹)^3)*(n:ℝ)^3*(D:ℝ)+
        2*(sum3 (fun a b (_:Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b))+
        sum3 (fun a (_:Fin n) c => matTrace (P.proj a*R.proj c*P.proj a*R.proj c))+
        sum3 (fun (_:Fin n) b c => matTrace (Q.proj b*R.proj c*Q.proj b*R.proj c))) := by
      rw [real_raw_trace_moment_4 hn P Q R]
      ring
    _ = _ := by
      rw [hpair]
      field_simp
      ring

theorem raw_five (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^5)) =
      (3*(n:ℝ)^2+60*(n:ℝ)+150+30/(n:ℝ))*(D:ℝ)+
        (10*(n:ℝ)+10)*totalSigma P Q R := by
  have hpair := total_pair_four hn P Q R
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  calc
    _ = (3*(n:ℝ)⁻¹+60*((n:ℝ)⁻¹)^2+120*((n:ℝ)⁻¹)^3)*(n:ℝ)^3*(D:ℝ)+
        (10+10*(n:ℝ)⁻¹)*(sum3 (fun a b (_:Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b))+
        sum3 (fun a (_:Fin n) c => matTrace (P.proj a*R.proj c*P.proj a*R.proj c))+
        sum3 (fun (_:Fin n) b c => matTrace (Q.proj b*R.proj c*Q.proj b*R.proj c))) := by
      rw [real_raw_trace_moment_5 hn P Q R]
      ring
    _ = _ := by
      rw [hpair]
      field_simp
      ring

theorem moment_four (hn : 0<n) (P Q R : PVM n D) :
    moment P Q R 4 = (D:ℝ)*(3/(n:ℝ)+36/(n:ℝ)^2+42/(n:ℝ)^3)+
      (2*(n:ℝ)*totalSigma P Q R)/(n:ℝ)^3 := by
  change sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^4))/(n:ℝ)^3 = _
  rw [raw_four hn P Q R]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  all_goals ring

theorem moment_five (hn : 0<n) (P Q R : PVM n D) :
    moment P Q R 5 = (D:ℝ)*(3/(n:ℝ)+60/(n:ℝ)^2+150/(n:ℝ)^3+30/(n:ℝ)^4)+
      ((10*(n:ℝ)+10)*totalSigma P Q R)/(n:ℝ)^3 := by
  change sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^5))/(n:ℝ)^3 = _
  rw [raw_five hn P Q R]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  all_goals ring

end FourMeas
end

section
open scoped BigOperators Matrix ComplexConjugate
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}
local notation "M" => Mat D

theorem trace_sum3_real (F : Fin n → Fin n → Fin n → M) :
    (∑ a, ∑ b, ∑ c, matTrace (F a b c)) = matTrace (sum3 F) := by
  simp [sum3, matTrace, Matrix.trace_sum, Complex.re_sum]

theorem sum3_qpqr (P Q R : PVM n D) :
    sum3 (fun a b c => Q.proj b*P.proj a*Q.proj b*R.proj c) = 1 := by
  unfold sum3
  simp_rw [← Finset.mul_sum, R.complete, mul_one]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Finset.mul_sum, P.complete, mul_one]
  simp_rw [(Q.isProj _).isIdempotentElem.eq]
  exact Q.complete

theorem sum3_qrpr (P Q R : PVM n D) :
    sum3 (fun a b c => Q.proj b*R.proj c*P.proj a*R.proj c) = 1 := by
  unfold sum3
  calc
    _ = ∑ b, ∑ c, ∑ a, Q.proj b*R.proj c*P.proj a*R.proj c := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, Q.proj b*R.proj c*R.proj c := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum, P.complete, mul_one]
    _ = 1 := by
      simp_rw [mul_assoc, (R.isProj _).isIdempotentElem.eq]
      simp only [← Finset.mul_sum, R.complete, mul_one, Q.complete]

theorem sum3_qr (P Q R : PVM n D) :
    sum3 (fun (_a : Fin n) b c => Q.proj b*R.proj c) = (n:ℝ) • (1:M) := by
  simp only [sum3, ← Finset.mul_sum, R.complete, mul_one, Q.complete,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul ℝ n (1:M)).symm

theorem anchorRho_word {n D : ℕ} (P Q R : PVM n D) (hn : n ≠ 0) :
    (∑ a, ∑ b, ∑ c, matTrace
      (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b)) =
      (D:ℝ)/(n:ℝ) + anchorRho P Q R := by
  have hcyc (a b c : Fin n) :
      Matrix.trace (Q.proj b*P.proj a*Q.proj b*(R.proj c*P.proj a*R.proj c)) =
      Matrix.trace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b) := by
    simpa only [mul_assoc] using FourMeasWords.cyclic_qpqrpr (P.proj a) (Q.proj b)
      (R.proj c) (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq
      (R.isProj c).isIdempotentElem.eq
  have hex : anchorRho P Q R =
      (∑ a, ∑ b, ∑ c, matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b)) -
      (n:ℝ)⁻¹*matTrace (sum3 (fun a b c => Q.proj b*P.proj a*Q.proj b*R.proj c)) -
      (n:ℝ)⁻¹*matTrace (sum3 (fun a b c => Q.proj b*R.proj c*P.proj a*R.proj c)) +
      ((n:ℝ)⁻¹)^2*matTrace (sum3 (fun (_a : Fin n) b c => Q.proj b*R.proj c)) := by
    rw [← trace_sum3_real, ← trace_sum3_real, ← trace_sum3_real]
    unfold anchorRho pairDefect
    simp only [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, smul_smul,
      matTrace, Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, Complex.smul_re,
      smul_eq_mul, hcyc]
    simp only [mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [sum3_qpqr P Q R, sum3_qrpr P Q R, sum3_qr P Q R] at hex
  simp only [matTrace, Matrix.trace_one, Fintype.card_fin, Matrix.trace_smul,
    Complex.natCast_re, Complex.smul_re, smul_eq_mul] at hex
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hscale : ((n:ℝ)⁻¹)^2*((n:ℝ)*(D:ℝ)) = (D:ℝ)/(n:ℝ) := by field_simp
  rw [hscale] at hex
  simp only [div_eq_mul_inv] at hex ⊢
  simp only [matTrace]
  linarith

theorem trace_cycle_reverse_real (p q r : M) (hp : p*p=p) (hq : q*q=q) (hr : r*r=r)
    (hps : star p=p) (hqs : star q=q) (hrs : star r=r) :
    matTrace (p*r*q*p*r*q) = matTrace (p*q*r*p*q*r) := by
  have h := FourMeasWords.cyclic_rqprqp p q r hp hq hr
  have hs : (p*q*r*p*q*r)ᴴ = r*q*p*r*q*p := by
    change star (p*q*r*p*q*r) = _
    simp only [star_mul, hps,hqs,hrs, mul_assoc]
  unfold matTrace
  rw [← h, ← hs, Matrix.trace_conjTranspose]
  simp only [Complex.star_def, Complex.conj_re]

theorem trace_sandwich_square (p q r : M) (hp : p*p=p) (hq : q*q=q) (hr : r*r=r)
    (hps : star p=p) (hqs : star q=q) (hrs : star r=r) :
    matTrace ((p*(q*r+r*q)*p)^2) =
      2*matTrace (p*q*r*p*q*r)+2*matTrace (p*q*r*p*r*q) := by
  have hsq : (p*(q*r+r*q)*p)^2 = p*(q*r+r*q)*p*(q*r+r*q)*p := by
    calc
      _ = p*(q*r+r*q)*(p*p)*(q*r+r*q)*p := by noncomm_ring
      _ = _ := by rw [hp]
  have h1 := FourMeasWords.cyclic_pqrpqrp p q r hp hq hr
  have h2 := FourMeasWords.cyclic_pqrprqp p q r hp hq hr
  have h3 := FourMeasWords.cyclic_prqpqrp p q r hp hq hr
  have h4 := FourMeasWords.cyclic_prqprqp p q r hp hq hr
  have hrev := trace_cycle_reverse_real p q r hp hq hr hps hqs hrs
  rw [hsq]
  simp only [matTrace, mul_add, add_mul, Matrix.trace_add, Complex.add_re]
  simp only [mul_assoc] at h1 h2 h3 h4 ⊢
  rw [h1,h2,h3,h4]
  simp only [matTrace, mul_assoc] at hrev
  rw [hrev]
  ring

theorem centered_sandwich_square (p K : M) (s : ℝ)
    (hp : p*p=p) (hleft : p*K=K) (hright : K*p=K) :
    (K-s • p)^2 = K^2-(2*s) • K+s^2 • p := by
  simp only [pow_two, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    smul_smul, hp,hleft,hright]
  module

theorem sum3_sandwich_symm (P Q R : PVM n D) :
    sum3 (fun a b c => P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a) =
      (2:ℝ) • (1:M) := by
  have hterm (a : Fin n) :
      (∑ b, ∑ c, P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a) =
      P.proj a+P.proj a := by
    simp only [mul_add, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, R.complete, Q.complete, one_mul, mul_one,
      (P.isProj a).isIdempotentElem.eq]
  simp only [sum3, hterm, Finset.sum_add_distrib, P.complete]
  module

theorem sum3_anchor (P Q R : PVM n D) :
    sum3 (fun a (_b _c : Fin n) => P.proj a) = (n:ℝ)^2 • (1:M) := by
  exact MUMMoments.short1 P.proj P.complete

theorem anchorVariance_cycle (P Q R : PVM n D) (hn : n ≠ 0) :
    matTrace (cycle P Q R) = ((2-(n:ℝ))/(n:ℝ)^2)*(D:ℝ) +
      anchorVariance P Q R/2-anchorRho P Q R := by
  have hpoint (a b c : Fin n) :
      matTrace ((defect P Q R a b c)^2) =
      2*matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c) +
      2*matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b) -
      (4/(n:ℝ)^2)*matTrace (P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a) +
      (4/(n:ℝ)^4)*matTrace (P.proj a) := by
    have hleft : P.proj a*(P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a) =
        P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a := by
      rw [← mul_assoc, ← mul_assoc, (P.isProj a).isIdempotentElem.eq]
    have hright : (P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a)*P.proj a =
        P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a := by
      rw [mul_assoc _ (P.proj a) (P.proj a), (P.isProj a).isIdempotentElem.eq]
    rw [defect, centered_sandwich_square _ _ _ (P.isProj a).isIdempotentElem.eq hleft hright]
    simp only [matTrace, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul]
    have hsq := trace_sandwich_square (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq
      (R.isProj c).isIdempotentElem.eq (P.isProj a).isSelfAdjoint.star_eq
      (Q.isProj b).isSelfAdjoint.star_eq (R.isProj c).isSelfAdjoint.star_eq
    unfold matTrace at hsq
    rw [hsq]
    ring
  have hsum := congrArg (fun F : Fin n → Fin n → Fin n → ℝ => ∑ a, ∑ b, ∑ c, F a b c)
    (funext fun a => funext fun b => funext fun c => hpoint a b c)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  change anchorVariance P Q R = _ at hsum
  rw [anchorRho_word P Q R hn] at hsum
  rw [trace_sum3_real, trace_sum3_real, trace_sum3_real,
    sum3_sandwich_symm P Q R, sum3_anchor P Q R] at hsum
  change anchorVariance P Q R = 2*matTrace (cycle P Q R)+
    2*((D:ℝ)/(n:ℝ)+anchorRho P Q R)-_+_ at hsum
  simp only [matTrace, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Complex.smul_re, Complex.natCast_re, smul_eq_mul] at hsum
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn
  have hscale : (4/(n:ℝ)^4)*((n:ℝ)^2*(D:ℝ)) = (4/(n:ℝ)^2)*(D:ℝ) := by field_simp
  rw [hscale] at hsum
  have hscale2 : (D:ℝ)/(n:ℝ) - 2*(D:ℝ)/(n:ℝ)^2 =
      -((2-(n:ℝ))/(n:ℝ)^2)*(D:ℝ) := by field_simp; ring
  unfold matTrace
  linear_combination -hsum / 2 - hscale2

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}

theorem sum3_rho_p (hn : 0 < n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b)) =
      (D:ℝ)/(n:ℝ)+anchorRho P Q R :=
  anchorRho_word P Q R (Nat.ne_of_gt hn)

theorem sum3_rho_q (hn : 0 < n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c)) =
      (D:ℝ)/(n:ℝ)+anchorRho Q R P := by
  have h := anchorRho_word Q R P (Nat.ne_of_gt hn)
  change sum3 (fun a b c => matTrace (Q.proj a*R.proj b*P.proj c*Q.proj a*P.proj c*R.proj b)) = _ at h
  rw [← sum3_bca (fun a b c => matTrace (Q.proj a*R.proj b*P.proj c*Q.proj a*P.proj c*R.proj b))] at h
  have hc (a b c : Fin n) :
      matTrace (Q.proj b*R.proj c*P.proj a*Q.proj b*P.proj a*R.proj c) =
      matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c) :=
    congrArg Complex.re (FourMeasWords.cyclic_qrpqpr (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc] at h
  exact h

theorem sum3_rho_r (hn : 0 < n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a*R.proj c)) =
      (D:ℝ)/(n:ℝ)+anchorRho R P Q := by
  have h := anchorRho_word R P Q (Nat.ne_of_gt hn)
  change sum3 (fun a b c => matTrace (R.proj a*P.proj b*Q.proj c*R.proj a*Q.proj c*P.proj b)) = _ at h
  rw [← sum3_cab (fun a b c => matTrace (R.proj a*P.proj b*Q.proj c*R.proj a*Q.proj c*P.proj b))] at h
  have hc (a b c : Fin n) :
      matTrace (R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a) =
      matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a*R.proj c) :=
    congrArg Complex.re (FourMeasWords.cyclic_rpqrqp (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc] at h
  exact h

theorem sum3_cycle_forward (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c)) =
      matTrace (cycle P Q R) := by
  simp only [sum3, cycle, matTrace, Matrix.trace_sum, Complex.re_sum]

theorem sum3_cycle_reverse (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b)) =
      matTrace (cycle P Q R) := by
  have hc (a b c : Fin n) := trace_cycle_reverse_real (P.proj a) (Q.proj b) (R.proj c)
    (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq
    (P.isProj a).isSelfAdjoint.star_eq (Q.isProj b).isSelfAdjoint.star_eq (R.isProj c).isSelfAdjoint.star_eq
  simp_rw [hc]
  exact sum3_cycle_forward P Q R

theorem cycle_aggregate_identity (hn : 0 < n) (P Q R : PVM n D) :
    6*matTrace (cycle P Q R) = 6*((2-(n:ℝ))/(n:ℝ)^2)*(D:ℝ) +
      totalVariance P Q R-2*totalRho P Q R := by
  have h1 := anchorVariance_cycle P Q R (Nat.ne_of_gt hn)
  have h2 := anchorVariance_cycle Q R P (Nat.ne_of_gt hn)
  have h3 := anchorVariance_cycle R P Q (Nat.ne_of_gt hn)
  have hc1 : matTrace (cycle P Q R) = matTrace (cycle Q R P) :=
    congrArg Complex.re (trace_cycle_cyclic P Q R)
  have hc2 : matTrace (cycle Q R P) = matTrace (cycle R P Q) :=
    congrArg Complex.re (trace_cycle_cyclic Q R P)
  rw [← hc1] at h2
  rw [← hc2, ← hc1] at h3
  unfold totalVariance totalRho
  linarith

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}

set_option maxHeartbeats 2000000 in
theorem moment_six (hn : 0 < n) (P Q R : PVM n D) :
    moment P Q R 6 = (D:ℝ)*(3/(n:ℝ)+90/(n:ℝ)^2+390/(n:ℝ)^3+234/(n:ℝ)^4+12/(n:ℝ)^5) +
      ((30*(n:ℝ)+78)*totalSigma P Q R+2*(n:ℝ)*totalKappa P Q R+
        totalVariance P Q R+4*totalRho P Q R)/(n:ℝ)^3 := by
  have hpr4 := sum3_pair_four hn P R Q
  rw [← sum3_acb (fun a b (_c : Fin n) => matTrace (P.proj a*R.proj b*P.proj a*R.proj b))] at hpr4
  have hqr4 := sum3_pair_four hn Q R P
  rw [← sum3_bca (fun a b (_c : Fin n) => matTrace (Q.proj a*R.proj b*Q.proj a*R.proj b))] at hqr4
  have hpr6 := sum3_pair_six hn P R Q
  rw [← sum3_acb (fun a b (_c : Fin n) => matTrace
    (P.proj a*R.proj b*P.proj a*R.proj b*P.proj a*R.proj b))] at hpr6
  have hqr6 := sum3_pair_six hn Q R P
  rw [← sum3_bca (fun a b (_c : Fin n) => matTrace
    (Q.proj a*R.proj b*Q.proj a*R.proj b*Q.proj a*R.proj b))] at hqr6
  have h := real_raw_trace_moment_6 hn P Q R
  rw [sum3_pair_four hn P Q R, sum3_pair_six hn P Q R,
    hpr4,hqr4,hpr6,hqr6, sum3_rho_p hn P Q R, sum3_rho_q hn P Q R,
    sum3_rho_r hn P Q R, sum3_cycle_forward P Q R, sum3_cycle_reverse P Q R] at h
  rw [pairSigma_symm P R, pairKappa_symm P R] at h
  have hc := cycle_aggregate_identity hn P Q R
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  change sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^6))/(n:ℝ)^3 = _
  rw [h]
  simp only [totalSigma, totalKappa, totalVariance, totalRho] at hc ⊢
  linear_combination (norm := skip) hc/(n:ℝ)^3
  field_simp
  ring

end FourMeas
end

section
open scoped BigOperators Matrix ComplexOrder
open Matrix
namespace FourMeasurementPositivity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_square_trace_nonneg (D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    0 ≤ (Matrix.trace (D * D)).re := by
  have hp : (D * D).PosSemidef := by
    simpa only [hD.eq] using Matrix.posSemidef_conjTranspose_mul_self D
  exact (Complex.nonneg_iff.mp hp.trace_nonneg).1

theorem supported_cubic_defect_nonneg (D P : Matrix ι ι ℂ) (c : ℝ)
    (hD : D.IsHermitian) (hDP : D * P = D)
    (hpos : (D + c • P).PosSemidef) :
    0 ≤ (Matrix.trace (D ^ 3)).re + c * (Matrix.trace (D ^ 2)).re := by
  have hp := hpos.conjTranspose_mul_mul_same D
  have hid : Dᴴ * (D + c • P) * D = D ^ 3 + c • D ^ 2 := by
    rw [hD.eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hDP]
    simp only [pow_succ, pow_zero, one_mul]
  rw [hid] at hp
  have hn := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  simpa only [Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
    Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using hn

theorem hermitian_cross_trace_lower (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    -((Matrix.trace (A*A)).re + (Matrix.trace (B*B)).re) / 2 ≤
      (Matrix.trace (A*B)).re := by
  have hp := hermitian_square_trace_nonneg (A+B) (hA.add hB)
  have he : (Matrix.trace ((A+B)*(A+B))).re =
      (Matrix.trace (A*A)).re + (Matrix.trace (B*B)).re +
      2 * (Matrix.trace (A*B)).re := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
    rw [Matrix.trace_mul_comm B A]
    ring
  rw [he] at hp
  linarith

theorem hermitian_cross_trace_sum_lower {α : Type*} [Fintype α]
    (A B : α → Matrix ι ι ℂ)
    (hA : ∀ a, (A a).IsHermitian) (hB : ∀ a, (B a).IsHermitian) :
    -((∑ a, (Matrix.trace (A a * A a)).re) +
      ∑ a, (Matrix.trace (B a * B a)).re)/2 ≤
      ∑ a, (Matrix.trace (A a * B a)).re := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    hermitian_cross_trace_lower (A a) (B a) (hA a) (hB a))
  simpa only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib] using h

theorem coefficient_kappa_pos (n x : ℝ) (hn : 2 ≤ n) (hx : 0 ≤ x) :
    0 < 2*n*x + 4*n + 14 := by positivity

theorem coefficient_B_lower (n x : ℝ) (hn : 2 ≤ n) (hx : 0 ≤ x)
    (hx2 : 81/16 < n*x^2) :
    121/4 < 2*n*x^3 + (4*n+10)*x^2 + (2*n+20)*x + 10 + 16/n := by
  have hn0 : 0 ≤ n := by linarith
  have h1 : 0 ≤ 2*n*x^3 := by positivity
  have h2 : 0 ≤ 10*x^2 := by positivity
  have h3 : 0 ≤ (2*n+20)*x := by positivity
  have h4 : 0 ≤ 16/n := by positivity
  nlinarith

theorem coefficient_penalty_upper (n x : ℝ) (hn : 2 ≤ n) (hx : 0 ≤ x) :
    490 / (9*(x+2)) * (1-1/n) ≤ 245/9 := by
  have hd : 0 < 9*(x+2) := by positivity
  have hc : 0 ≤ 490 / (9*(x+2)) := by positivity
  have hfrac : 490 / (9*(x+2)) ≤ 245/9 := by
    apply (div_le_iff₀ hd).2
    nlinarith
  have hfac : 1-1/n ≤ 1 := by
    have : 0 ≤ 1/n := by positivity
    linarith
  calc
    _ ≤ 490 / (9*(x+2)) * 1 := mul_le_mul_of_nonneg_left hfac hc
    _ ≤ 245/9 := by simpa using hfrac

theorem coefficient_gap (n x : ℝ) (hn : 2 ≤ n) (hx : 0 ≤ x)
    (hx2 : 81/16 < n*x^2) :
    3 < (2*n*x^3 + (4*n+10)*x^2 + (2*n+20)*x + 10 + 16/n) -
      490 / (9*(x+2)) * (1-1/n) := by
  have hB := coefficient_B_lower n x hn hx hx2
  have hP := coefficient_penalty_upper n x hn hx
  linarith

theorem aggregate_defect_lower_bound (n x s k v r z : ℝ)
    (hn : 2 ≤ n) (hx : 0 ≤ x) (hx2 : 81/16 < n*x^2)
    (hs : 0 ≤ s) (hv : 0 ≤ v) (hk : -s/n ≤ k) (hr : -s ≤ r)
    (hz : -(9*(x+2)/10*v + 490/(9*(x+2))*(1-1/n)*s) ≤ 14*z) :
    3*s + (x+2)*v/10 ≤
      (2*n*x^3+(4*n+10)*x^2+(2*n+26)*x+22+30/n)*s +
      (2*n*x+4*n+14)*k + (x+2)*(v+4*r) + 14*z := by
  have hn0 : n ≠ 0 := by linarith
  have hkc := coefficient_kappa_pos n x hn hx
  have hkm := mul_le_mul_of_nonneg_left hk hkc.le
  have hrm := mul_le_mul_of_nonneg_left hr (show 0 ≤ 4*(x+2) by positivity)
  have hgap := mul_le_mul_of_nonneg_right (coefficient_gap n x hn hx hx2).le hs
  have heq : (2*n*x^3+(4*n+10)*x^2+(2*n+26)*x+22+30/n) -
      (2*n*x+4*n+14)/n - 4*(x+2) =
      2*n*x^3+(4*n+10)*x^2+(2*n+20)*x+10+16/n := by
    field_simp
    <;> ring
  have hmul : (2*n*x+4*n+14)*(-s/n) = -((2*n*x+4*n+14)/n)*s := by ring
  rw [hmul] at hkm
  rw [← heq] at hgap
  nlinarith

end FourMeasurementPositivity
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem pairDefect_selfAdjoint (P Q : PVM n D) (a b : Fin n) :
    IsSelfAdjoint (pairDefect P Q a b) := by
  change star (pairDefect P Q a b) = pairDefect P Q a b
  simp only [pairDefect, star_sub, star_mul, star_smul, star_trivial,
    (P.isProj a).isSelfAdjoint.star_eq, (Q.isProj b).isSelfAdjoint.star_eq]
  noncomm_ring

theorem pairDefect_left_supported (P Q : PVM n D) (a b : Fin n) :
    P.proj a * pairDefect P Q a b = pairDefect P Q a b := by
  simp only [pairDefect, mul_sub, mul_smul_comm]
  rw [← mul_assoc, ← mul_assoc, (P.isProj a).isIdempotentElem]

theorem pairDefect_right_supported (P Q : PVM n D) (a b : Fin n) :
    pairDefect P Q a b * P.proj a = pairDefect P Q a b := by
  have h := congrArg star (pairDefect_left_supported P Q a b)
  simpa only [star_mul, (P.isProj a).isSelfAdjoint.star_eq,
    (pairDefect_selfAdjoint P Q a b).star_eq] using h

theorem pairSigma_nonneg (P Q : PVM n D) : 0 ≤ pairSigma P Q := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  have h := matrix_trace_mono (pairDefect_selfAdjoint P Q a b).sq_nonneg
  simpa only [matTrace, Matrix.trace_zero, Complex.zero_re] using h

theorem pairKappa_lower (P Q : PVM n D) :
    -(n:ℝ)⁻¹ * pairSigma P Q ≤ pairKappa P Q := by
  have hp (a b : Fin n) : 0 ≤ matTrace ((pairDefect P Q a b)^3) +
      (n:ℝ)⁻¹ * matTrace ((pairDefect P Q a b)^2) := by
    apply FourMeasurementPositivity.supported_cubic_defect_nonneg
      (pairDefect P Q a b) (P.proj a) (n:ℝ)⁻¹
      (pairDefect_selfAdjoint P Q a b) (pairDefect_right_supported P Q a b)
    have h := (Matrix.nonneg_iff_posSemidef.mp (Q.proj_nonneg b)).conjTranspose_mul_mul_same (P.proj a)
    simpa only [pairDefect, sub_add_cancel, ← Matrix.star_eq_conjTranspose,
      (P.isProj a).isSelfAdjoint.star_eq] using h
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun a _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun b _ => hp a b))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  change 0 ≤ pairKappa P Q + (n:ℝ)⁻¹ * pairSigma P Q at hsum
  linarith

theorem totalSigma_nonneg (P Q R : PVM n D) : 0 ≤ totalSigma P Q R := by
  exact add_nonneg (add_nonneg (pairSigma_nonneg P Q) (pairSigma_nonneg Q R)) (pairSigma_nonneg R P)

theorem totalKappa_lower (P Q R : PVM n D) :
    -(n:ℝ)⁻¹ * totalSigma P Q R ≤ totalKappa P Q R := by
  have h1 := pairKappa_lower P Q
  have h2 := pairKappa_lower Q R
  have h3 := pairKappa_lower R P
  unfold totalSigma totalKappa
  nlinarith

theorem anchorVariance_nonneg (P Q R : PVM n D) : 0 ≤ anchorVariance P Q R := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  have h := matrix_trace_mono (defect_selfAdjoint P Q R a b c).sq_nonneg
  simpa only [matTrace, Matrix.trace_zero, Complex.zero_re] using h

theorem totalVariance_nonneg (P Q R : PVM n D) : 0 ≤ totalVariance P Q R := by
  exact add_nonneg (add_nonneg (anchorVariance_nonneg P Q R) (anchorVariance_nonneg Q R P)) (anchorVariance_nonneg R P Q)

theorem pinched_pairDefect_selfAdjoint (P Q : PVM n D) (a : Fin n) :
    IsSelfAdjoint (∑ b, pairDefect Q P b a) := by
  change star (∑ b, pairDefect Q P b a) = _
  simp only [star_sum, (pairDefect_selfAdjoint Q P _ _).star_eq]

theorem pinched_pairDefect_square (P Q : PVM n D) (a : Fin n) :
    (∑ b, pairDefect Q P b a)^2 = ∑ b, (pairDefect Q P b a)^2 := by
  have h := orthogonal_supported_sum_square Q.proj (fun b => pairDefect Q P b a)
    Q.orthogonal (fun b => pairDefect_selfAdjoint Q P b a)
    (fun b => pairDefect_left_supported Q P b a)
    (fun b => pairDefect_right_supported Q P b a)
  simpa only [(pinched_pairDefect_selfAdjoint P Q a).star_eq, pow_two] using h

theorem anchorRho_lower_oriented (P Q R : PVM n D) :
    -(pairSigma Q P + pairSigma R P)/2 ≤ anchorRho P Q R := by
  let U (Q : PVM n D) (a : Fin n) := ∑ b, pairDefect Q P b a
  have he (Q : PVM n D) : (∑ a, (Matrix.trace (U Q a * U Q a)).re) = pairSigma Q P := by
    simp only [U, ← pow_two, pinched_pairDefect_square, Matrix.trace_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    rfl
  have hr : (∑ a, (Matrix.trace (U Q a * U R a)).re) = anchorRho P Q R := by
    simp only [U, anchorRho, matTrace, Finset.sum_mul, Finset.mul_sum,
      Matrix.trace_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_comm]
  have h := FourMeasurementPositivity.hermitian_cross_trace_sum_lower (U Q) (U R)
    (pinched_pairDefect_selfAdjoint P Q) (pinched_pairDefect_selfAdjoint P R)
  rw [he, he, hr] at h
  exact h

end
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

def anchorKernel (P Q R : PVM n D) (a b c : Fin n) : Mat D :=
  P.proj a * (Q.proj b * R.proj c + R.proj c * Q.proj b) * P.proj a

theorem pairDefect_sum (hn : 0 < n) (P Q : PVM n D) (a : Fin n) :
    ∑ b, pairDefect P Q a b = 0 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp only [pairDefect, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Q.complete, mul_one, (P.isProj a).isIdempotentElem.eq,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0, one_smul, sub_self]

theorem anchorKernel_sum_right (P Q R : PVM n D) (a b : Fin n) :
    ∑ c, anchorKernel P Q R a b c = (2:ℝ) • (P.proj a * Q.proj b * P.proj a) := by
  simp only [anchorKernel, mul_add, add_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, R.complete, mul_one, one_mul]
  module

theorem anchorKernel_sum_left (P Q R : PVM n D) (a c : Fin n) :
    ∑ b, anchorKernel P Q R a b c = (2:ℝ) • (P.proj a * R.proj c * P.proj a) := by
  simp only [anchorKernel, mul_add, add_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Q.complete, mul_one, one_mul]
  module

private theorem aux8_trace_three_reverse (A B C : Mat D)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (hC : IsSelfAdjoint C) :
    matTrace (A*B*C) = matTrace (C*B*A) := by
  have h := Matrix.trace_conjTranspose (A*B*C)
  have hs : (A*B*C).conjTranspose = C*B*A := by
    change star (A*B*C) = _
    simp only [star_mul,hA.star_eq,hB.star_eq,hC.star_eq,mul_assoc]
  rw [hs] at h
  have hr := congrArg Complex.re h
  simpa only [matTrace, Complex.star_def, Complex.conj_re] using hr.symm

private theorem aux9_trace_three_rotate (A B C : Mat D) :
    matTrace (A*B*C) = matTrace (C*A*B) := by
  unfold matTrace
  congr 1
  simpa only [mul_assoc] using Matrix.trace_mul_comm (A*B) C

theorem anchorKernel_selfAdjoint (P Q R : PVM n D) (a b c : Fin n) :
    IsSelfAdjoint (anchorKernel P Q R a b c) := by
  change star (anchorKernel P Q R a b c) = _
  simp only [anchorKernel,star_mul,star_add,(P.isProj a).isSelfAdjoint.star_eq,
    (Q.isProj b).isSelfAdjoint.star_eq,(R.isProj c).isSelfAdjoint.star_eq]
  noncomm_ring

private theorem aux10_supported_expand (p U V X Y K : Mat D) (u : ℝ)
    (hp : p*p=p) (hX : p*X=X) (hXp : X*p=X) (hY : p*Y=Y) (hYp : Y*p=Y)
    (hK : K*p=K) (hU : U=X+u•p) (hV : V=Y+u•p) :
    K*(U*V+V*U) = (2*u^2)•K + (2*u)•(K*X) + (2*u)•(K*Y) +
      K*X*Y+K*Y*X := by
  rw [hU,hV]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hp,hX,hXp,hY,hYp,hK]
  simp only [smul_add,smul_smul,mul_assoc]
  module

theorem anchor_seven_point (P Q R : PVM n D) (a b c : Fin n) :
    matTrace (anchorKernel P Q R a b c *
      ((P.proj a*Q.proj b*P.proj a)*(P.proj a*R.proj c*P.proj a)+
       (P.proj a*R.proj c*P.proj a)*(P.proj a*Q.proj b*P.proj a))) =
    (2*((n:ℝ)⁻¹)^2)*matTrace (anchorKernel P Q R a b c) +
    (2*(n:ℝ)⁻¹)*matTrace (anchorKernel P Q R a b c * pairDefect P Q a b) +
    (2*(n:ℝ)⁻¹)*matTrace (anchorKernel P Q R a b c * pairDefect P R a c) +
    2*matTrace (pairDefect P R a c * defect P Q R a b c * pairDefect P Q a b) +
    (4/(n:ℝ)^2)*matTrace (pairDefect P R a c * pairDefect P Q a b) := by
  let X := pairDefect P Q a b
  let Y := pairDefect P R a c
  let K := anchorKernel P Q R a b c
  have hK : K*P.proj a=K := by
    simp only [K,anchorKernel,mul_assoc,(P.isProj a).isIdempotentElem.eq]
  have hU : P.proj a*Q.proj b*P.proj a=X+(n:ℝ)⁻¹•P.proj a := by dsimp [X,pairDefect]; module
  have hV : P.proj a*R.proj c*P.proj a=Y+(n:ℝ)⁻¹•P.proj a := by dsimp [Y,pairDefect]; module
  rw [aux10_supported_expand (P.proj a) _ _ X Y K (n:ℝ)⁻¹
    (P.isProj a).isIdempotentElem.eq (pairDefect_left_supported P Q a b)
    (pairDefect_right_supported P Q a b) (pairDefect_left_supported P R a c)
    (pairDefect_right_supported P R a c) hK hU hV]
  have ht : matTrace (K*X*Y)=matTrace (K*Y*X) := by
    rw [aux8_trace_three_reverse K X Y (anchorKernel_selfAdjoint P Q R a b c)
      (pairDefect_selfAdjoint P Q a b) (pairDefect_selfAdjoint P R a c)]
    exact aux9_trace_three_rotate Y X K
  have hdef : K=defect P Q R a b c+(2/(n:ℝ)^2)•P.proj a := by
    dsimp [K,anchorKernel,defect]; module
  have he : matTrace (K*X*Y)=
      matTrace (Y*defect P Q R a b c*X)+(2/(n:ℝ)^2)*matTrace (Y*X) := by
    rw [aux9_trace_three_rotate K X Y,hdef,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
    rw [pairDefect_right_supported P R a c]
    simp only [matTrace,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,
      Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  simp only [matTrace,Matrix.trace_add,Matrix.trace_smul,Complex.add_re,
    Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at ht he ⊢
  dsimp [X,Y,K] at ht he ⊢
  rw [← ht,he]
  ring

theorem anchorKernel_trace_sum (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,matTrace (anchorKernel P Q R a b c)) = 2*(D:ℝ) := by
  simp only [matTrace, ← Complex.re_sum, ← Matrix.trace_sum, anchorKernel_sum_right,
    ← Finset.smul_sum, ← Finset.sum_mul, ← Finset.mul_sum, Q.complete, mul_one,
    (P.isProj _).isIdempotentElem.eq, P.complete, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,Complex.natCast_re]

theorem anchorKernel_pair_sum (hn : 0<n) (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,matTrace (anchorKernel P Q R a b c * pairDefect P Q a b)) =
      2*pairSigma P Q := by
  have hprod (a b : Fin n) :
      (P.proj a*Q.proj b*P.proj a)*pairDefect P Q a b =
      (pairDefect P Q a b)^2+(n:ℝ)⁻¹•pairDefect P Q a b := by
    have he : P.proj a*Q.proj b*P.proj a =
        pairDefect P Q a b+(n:ℝ)⁻¹•P.proj a := by unfold pairDefect; module
    conv_lhs => rw [he,add_mul,smul_mul_assoc,pairDefect_left_supported,← pow_two]
  simp only [matTrace,← Complex.re_sum,← Matrix.trace_sum,← Finset.sum_mul,
    anchorKernel_sum_right,smul_mul_assoc,hprod]
  simp only [Finset.sum_add_distrib,← Finset.smul_sum,pairDefect_sum hn,smul_zero,
    add_zero,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp only [pairSigma,matTrace,Matrix.trace_sum,Complex.re_sum]

theorem anchorKernel_pair_sum' (hn : 0<n) (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,matTrace (anchorKernel P Q R a b c * pairDefect P R a c)) =
      2*pairSigma P R := by
  have he (a b c : Fin n) : anchorKernel P Q R a b c=anchorKernel P R Q a c b := by
    unfold anchorKernel
    rw [add_comm]
  simp_rw [he,Finset.sum_comm (f := fun b c => matTrace
    (anchorKernel P R Q _ c b * pairDefect P R _ c))]
  exact anchorKernel_pair_sum hn P R Q

theorem pairDefect_cross_sum (hn : 0<n) (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,matTrace (pairDefect P R a c * pairDefect P Q a b))=0 := by
  simp only [matTrace,← Complex.re_sum,← Matrix.trace_sum,← Finset.sum_mul,
    pairDefect_sum hn,zero_mul,Finset.sum_const_zero,Matrix.trace_zero,Complex.zero_re]

theorem anchor_seven_sandwich (hn : 0<n) (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,matTrace (anchorKernel P Q R a b c *
      ((P.proj a*Q.proj b*P.proj a)*(P.proj a*R.proj c*P.proj a)+
       (P.proj a*R.proj c*P.proj a)*(P.proj a*Q.proj b*P.proj a)))) =
    4*(D:ℝ)/(n:ℝ)^2 + (4/(n:ℝ))*(pairSigma P Q+pairSigma P R)+
      2*anchorXi P Q R := by
  simp_rw [anchor_seven_point]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,anchorKernel_trace_sum,
    anchorKernel_pair_sum hn,anchorKernel_pair_sum' hn,pairDefect_cross_sum hn,
    mul_zero,add_zero]
  unfold anchorXi
  ring

private theorem aux11_idem_tail (p z : Mat D) (hp : p*p=p) : p*(p*z)=p*z := by
  rw [← mul_assoc,hp]

theorem anchor_seven_words_point (p q r : Mat D) (hp : p*p=p) :
    matTrace ((p*(q*r+r*q)*p)*((p*q*p)*(p*r*p)+(p*r*p)*(p*q*p))) =
    matTrace (p*q*r*p*q*p*r) + matTrace (p*q*r*p*r*p*q) +
    matTrace (p*r*q*p*q*p*r) + matTrace (p*r*q*p*r*p*q) := by
  have hm : (p*(q*r+r*q)*p)*((p*q*p)*(p*r*p)+(p*r*p)*(p*q*p)) =
      p*(q*r*p*q*p*r+q*r*p*r*p*q+r*q*p*q*p*r+r*q*p*r*p*q)*p := by
    simp only [mul_add,add_mul,mul_assoc,aux11_idem_tail p _ hp]
    abel
  rw [hm]
  unfold matTrace
  rw [PairTraceIdentities.sandwich_trace p _ hp]
  simp only [mul_add,Matrix.trace_add,Complex.add_re,mul_assoc]

theorem anchor_seven_identity (hn : 0<n) (P Q R : PVM n D) :
    (∑ a,∑ b,∑ c,
      (matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*P.proj a*R.proj c) +
       matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*P.proj a*Q.proj b) +
       matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*Q.proj b*P.proj a*R.proj c) +
       matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*P.proj a*Q.proj b))) =
    4*(D:ℝ)/(n:ℝ)^2+(4/(n:ℝ))*(pairSigma P Q+pairSigma P R)+2*anchorXi P Q R := by
  have h := anchor_seven_sandwich hn P Q R
  unfold anchorKernel at h
  simpa only [anchor_seven_words_point _ _ _ (P.isProj _).isIdempotentElem.eq] using h

end
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}
set_option maxHeartbeats 2000000

theorem seven_group_p (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c)) = 4*(D:ℝ)/(n:ℝ)^2+(4/(n:ℝ))*(pairSigma P Q+pairSigma P R)+2*anchorXi P Q R := by
  have h := anchor_seven_identity hn P Q R
  have hc0 (a b c : Fin n) : matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*P.proj a*R.proj c) = matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*Q.proj b*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_pqrpqpr (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc0] at h
  have hc1 (a b c : Fin n) : matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*P.proj a*Q.proj b) = matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_pqrprpq (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc1] at h
  have hc2 (a b c : Fin n) : matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*Q.proj b*P.proj a*R.proj c) = matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_prqpqpr (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc2] at h
  have hc3 (a b c : Fin n) : matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*P.proj a*Q.proj b) = matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_prqprpq (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc3] at h
  simpa only [sum3,Finset.sum_add_distrib] using h

theorem seven_group_q (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b)) = 4*(D:ℝ)/(n:ℝ)^2+(4/(n:ℝ))*(pairSigma Q R+pairSigma Q P)+2*anchorXi Q R P := by
  have h := anchor_seven_identity hn Q R P
  change sum3 (fun b c a => matTrace (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a) + matTrace (Q.proj b*R.proj c*P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c) + matTrace (Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b*P.proj a) + matTrace (Q.proj b*P.proj a*R.proj c*Q.proj b*P.proj a*Q.proj b*R.proj c)) = _ at h
  rw [sum3_cab] at h
  have hc0 (a b c : Fin n) : matTrace (Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a) = matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_qrpqrqp (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc0] at h
  have hc1 (a b c : Fin n) : matTrace (Q.proj b*R.proj c*P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c) = matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_qrpqpqr (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc1] at h
  have hc2 (a b c : Fin n) : matTrace (Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b*P.proj a) = matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_qprqrqp (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc2] at h
  have hc3 (a b c : Fin n) : matTrace (Q.proj b*P.proj a*R.proj c*Q.proj b*P.proj a*Q.proj b*R.proj c) = matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_qprqpqr (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc3] at h
  simpa only [sum3,Finset.sum_add_distrib] using h

theorem seven_group_r (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c*P.proj a*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c)) = 4*(D:ℝ)/(n:ℝ)^2+(4/(n:ℝ))*(pairSigma R P+pairSigma R Q)+2*anchorXi R P Q := by
  have h := anchor_seven_identity hn R P Q
  change sum3 (fun c a b => matTrace (R.proj c*P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b) + matTrace (R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c*P.proj a) + matTrace (R.proj c*Q.proj b*P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b) + matTrace (R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*P.proj a)) = _ at h
  rw [sum3_bca] at h
  have hc0 (a b c : Fin n) : matTrace (R.proj c*P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b) = matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_rpqrprq (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc0] at h
  have hc1 (a b c : Fin n) : matTrace (R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c*P.proj a) = matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c*P.proj a*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_rpqrqrp (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc1] at h
  have hc2 (a b c : Fin n) : matTrace (R.proj c*Q.proj b*P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b) = matTrace (P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_rqprprq (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc2] at h
  have hc3 (a b c : Fin n) : matTrace (R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*P.proj a) = matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c) := by
    exact congrArg Complex.re (FourMeasWords.cyclic_rqprqrp (P.proj a) (Q.proj b) (R.proj c)
      (P.isProj a).isIdempotentElem.eq (Q.isProj b).isIdempotentElem.eq (R.isProj c).isIdempotentElem.eq)
  simp_rw [hc3] at h
  simpa only [sum3,Finset.sum_add_distrib] using h

theorem seven_groups_total (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*Q.proj b*R.proj c*Q.proj b*R.proj c*P.proj a*R.proj c)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*R.proj c*P.proj a*R.proj c*Q.proj b*R.proj c*Q.proj b)) + sum3 (fun (a b c : Fin n) => matTrace (P.proj a*R.proj c*Q.proj b*P.proj a*R.proj c*Q.proj b*R.proj c)) =
    12*(D:ℝ)/(n:ℝ)^2+(8/(n:ℝ))*totalSigma P Q R+2*totalXi P Q R := by
  have h1 := seven_group_p hn P Q R
  have h2 := seven_group_q hn P Q R
  have h3 := seven_group_r hn P Q R
  rw [pairSigma_symm P R] at h1
  rw [pairSigma_symm Q P] at h2
  rw [pairSigma_symm R Q] at h3
  unfold totalSigma totalXi
  linear_combination h1+h2+h3
end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}
set_option maxHeartbeats 3000000

theorem raw_seven_from_six (hn : 0<n) (P Q R : PVM n D) :
    sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^7)) =
    7*sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^6)) +
    (-18*(n:ℝ)^2-504*(n:ℝ)-1470)*(D:ℝ) +
    (-140-210/(n:ℝ))*((n:ℝ)*totalSigma P Q R+3*(D:ℝ)) +
    (14/(n:ℝ))*((n:ℝ)*totalKappa P Q R+3*totalSigma P Q R+3*(D:ℝ)/(n:ℝ)) +
    7*(12*(D:ℝ)/(n:ℝ)^2+(8/(n:ℝ))*totalSigma P Q R+2*totalXi P Q R) := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have h6 := real_raw_trace_moment_6 hn P Q R
  have h7 := real_raw_trace_moment_7 hn P Q R
  have hg := seven_groups_total hn P Q R
  have h4 := total_pair_four hn P Q R
  have hp6 := total_pair_six hn P Q R
  linear_combination (norm := skip) h7-7*h6+7*hg+(-140-210/(n:ℝ))*h4+(14/(n:ℝ))*hp6
  field_simp
  ring

end FourMeas
end

section
open scoped BigOperators
namespace FourMeas
open MUMSpectral MUMMoments
variable {n D : ℕ}
set_option maxHeartbeats 3000000

theorem moment_seven (hn : 0<n) (P Q R : PVM n D) :
    moment P Q R 7 = (D:ℝ)*(3/(n:ℝ)+126/(n:ℝ)^2+840/(n:ℝ)^3+
      1008/(n:ℝ)^4+210/(n:ℝ)^5) +
      ((70*(n:ℝ)+336+98/(n:ℝ))*totalSigma P Q R+(14*(n:ℝ)+14)*totalKappa P Q R+
        7*totalVariance P Q R+28*totalRho P Q R+14*totalXi P Q R)/(n:ℝ)^3 := by
  have hnR : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hn
  have h6 := moment_six hn P Q R
  have h7 := raw_seven_from_six hn P Q R
  change sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^6))/(n:ℝ)^3 = _ at h6
  change sum3 (fun a b c => matTrace ((P.proj a+Q.proj b+R.proj c)^7))/(n:ℝ)^3 = _
  linear_combination (norm := skip) h7/(n:ℝ)^3+7*h6
  field_simp
  ring

end FourMeas
end

section
open scoped BigOperators Matrix ComplexOrder
namespace FourMeas
open MUMSpectral FourMeasScalars
variable {n D : ℕ}

theorem moment_eq_trace_average (P Q R : PVM n D) (k : ℕ) :
    moment P Q R k = matTrace (matrixAverage fun abc => (tripleSum P Q R abc)^k) := by
  unfold moment matTrace matrixAverage tripleSum
  simp only [Matrix.trace_smul, Complex.smul_re, smul_eq_mul, Matrix.trace_sum,
    Complex.re_sum, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
    Fintype.sum_prod_type]
  ring

theorem moment_one (hn : 0 < n) (P Q R : PVM n D) :
    moment P Q R 1 = (D:ℝ)*(3/(n:ℝ)) := by
  rw [moment_eq_trace_average]
  simp only [pow_one]
  rw [(Harmonic.normalized_low_moments P Q R (Nat.ne_of_gt hn)).1]
  simp only [matTrace, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Complex.smul_re, Complex.natCast_re, smul_eq_mul]
  ring

theorem moment_two (hn : 0 < n) (P Q R : PVM n D) :
    moment P Q R 2 = (D:ℝ)*(3/(n:ℝ)+6/(n:ℝ)^2) := by
  rw [moment_eq_trace_average, (Harmonic.normalized_low_moments P Q R (Nat.ne_of_gt hn)).2.1]
  simp only [matTrace, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Complex.smul_re, Complex.natCast_re, smul_eq_mul]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

theorem moment_three (hn : 0 < n) (P Q R : PVM n D) :
    moment P Q R 3 = (D:ℝ)*(3/(n:ℝ)+18/(n:ℝ)^2+6/(n:ℝ)^3) := by
  rw [moment_eq_trace_average, (Harmonic.normalized_low_moments P Q R (Nat.ne_of_gt hn)).2.2]
  simp only [matTrace, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    Complex.smul_re, Complex.natCast_re, smul_eq_mul]
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  ring

set_option maxHeartbeats 2000000 in
theorem Phi_expansion_of_moments (hn : 0 < n) (P Q R : PVM n D) (lam : ℝ)
    (h4 : moment P Q R 4 = (D:ℝ)*(3/(n:ℝ)+36/(n:ℝ)^2+42/(n:ℝ)^3) +
      (2*(n:ℝ)*totalSigma P Q R)/(n:ℝ)^3)
    (h5 : moment P Q R 5 = (D:ℝ)*(3/(n:ℝ)+60/(n:ℝ)^2+150/(n:ℝ)^3+30/(n:ℝ)^4) +
      ((10*(n:ℝ)+10)*totalSigma P Q R)/(n:ℝ)^3)
    (h6 : moment P Q R 6 = (D:ℝ)*(3/(n:ℝ)+90/(n:ℝ)^2+390/(n:ℝ)^3+234/(n:ℝ)^4+12/(n:ℝ)^5) +
      ((30*(n:ℝ)+78)*totalSigma P Q R+2*(n:ℝ)*totalKappa P Q R+
        totalVariance P Q R+4*totalRho P Q R)/(n:ℝ)^3)
    (h7 : moment P Q R 7 = (D:ℝ)*(3/(n:ℝ)+126/(n:ℝ)^2+840/(n:ℝ)^3+1008/(n:ℝ)^4+210/(n:ℝ)^5) +
      ((70*(n:ℝ)+336+98/(n:ℝ))*totalSigma P Q R+(14*(n:ℝ)+14)*totalKappa P Q R+
        7*totalVariance P Q R+28*totalRho P Q R+14*totalXi P Q R)/(n:ℝ)^3) :
    (n:ℝ)^3*Phi P Q R lam =
      (2*(n:ℝ)*(lam-1)^3+(4*(n:ℝ)+10)*(lam-1)^2+(2*(n:ℝ)+26)*(lam-1)+22+30/(n:ℝ))*totalSigma P Q R +
      (2*(n:ℝ)*(lam-1)+4*(n:ℝ)+14)*totalKappa P Q R +
      ((lam-1)+2)*(totalVariance P Q R+4*totalRho P Q R)+14*totalXi P Q R := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hi := ideal_moment_cancellation (n:ℝ) lam hnR
  have hw := weighted_defect_expansion (n:ℝ) (lam-1) (totalSigma P Q R)
    (totalKappa P Q R) (totalVariance P Q R) (totalRho P Q R) (totalXi P Q R) hnR
  simp only [sub_add_cancel] at hw
  rw [Phi_eq_moments, moment_one hn P Q R, moment_two hn P Q R,
    moment_three hn P Q R, h4,h5,h6,h7]
  linear_combination (norm := skip) (n:ℝ)^3*(D:ℝ)*hi+hw
  field_simp
  ring

theorem Phi_eq_defects (hn : 0 < n) (P Q R : PVM n D) (lam : ℝ) :
    (n:ℝ)^3*Phi P Q R lam =
      (2*(n:ℝ)*(lam-1)^3+(4*(n:ℝ)+10)*(lam-1)^2+(2*(n:ℝ)+26)*(lam-1)+22+30/(n:ℝ))*totalSigma P Q R +
      (2*(n:ℝ)*(lam-1)+4*(n:ℝ)+14)*totalKappa P Q R +
      ((lam-1)+2)*(totalVariance P Q R+4*totalRho P Q R)+14*totalXi P Q R :=
  Phi_expansion_of_moments hn P Q R lam (moment_four hn P Q R) (moment_five hn P Q R)
    (moment_six hn P Q R) (moment_seven hn P Q R)

end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem matTrace_star (A : Mat D) : matTrace (star A) = matTrace A := by
  simp only [matTrace, Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]
  rfl

theorem trace_young_lower (E Z : Mat D) (hE : IsSelfAdjoint E)
    (eps : ℝ) (heps : 0 < eps) :
    -(eps * matTrace (E^2) + matTrace (Z * star Z)/eps)/2 ≤ matTrace (E*Z) := by
  have hcross : matTrace (star Z * E) = matTrace (E * Z) := by
    have h := matTrace_star (E * Z)
    simpa only [star_mul, hE.star_eq] using h
  have hp := matrix_trace_mono (mul_star_self_nonneg (eps • E + star Z))
  have he : matTrace ((eps • E + star Z)*star (eps • E + star Z)) =
      eps^2 * matTrace (E^2) + 2*eps*matTrace (E*Z) + matTrace (Z*star Z) := by
    simp only [star_add, star_smul, star_trivial, star_star, hE.star_eq,
      add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul]
    simp only [matTrace, Matrix.trace_add, Matrix.trace_smul, Complex.add_re,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, pow_two]
    change eps * (eps * matTrace (E*E) + matTrace (star Z * E)) +
      (eps * matTrace (E*Z) + matTrace (star Z * Z)) = _
    rw [hcross]
    have hc : matTrace (star Z * Z) = matTrace (Z * star Z) := by
      unfold matTrace
      rw [Matrix.trace_mul_comm]
    rw [hc]
    dsimp only [matTrace]
    ring
  change (Matrix.trace (0 : Mat D)).re ≤ matTrace _ at hp
  simp only [Matrix.trace_zero, Complex.zero_re, he] at hp
  have hcancel : (matTrace (Z*star Z)/eps)*eps = matTrace (Z*star Z) :=
    div_mul_cancel₀ _ heps.ne'
  apply (mul_le_mul_iff_right₀ heps).mp
  nlinarith

end
end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem compression_square_le (P Q : PVM n D) (a b : Fin n) :
    (P.proj a * Q.proj b * P.proj a)^2 ≤ P.proj a * Q.proj b * P.proj a := by
  have h := projection_sandwich_le (P.proj a * Q.proj b) (P.proj a) (P.isProj a)
  have hl : (P.proj a * Q.proj b * P.proj a)^2 =
      (P.proj a * Q.proj b) * P.proj a * star (P.proj a * Q.proj b) := by
    simp only [star_mul, (P.isProj a).isSelfAdjoint.star_eq,
      (Q.isProj b).isSelfAdjoint.star_eq, pow_two]
    calc
      _ = P.proj a * Q.proj b * (P.proj a * P.proj a) * Q.proj b * P.proj a := by noncomm_ring
      _ = _ := by rw [(P.isProj a).isIdempotentElem]; noncomm_ring
  have hr : (P.proj a * Q.proj b) * star (P.proj a * Q.proj b) =
      P.proj a * Q.proj b * P.proj a := by
    simp only [star_mul, (P.isProj a).isSelfAdjoint.star_eq,
      (Q.isProj b).isSelfAdjoint.star_eq]
    calc
      _ = P.proj a * (Q.proj b * Q.proj b) * P.proj a := by noncomm_ring
      _ = _ := by rw [(Q.isProj b).isIdempotentElem]
  rwa [← hl, hr] at h

theorem pairDefect_square_expand (P Q : PVM n D) (a b : Fin n) :
    (pairDefect P Q a b)^2 =
      (P.proj a * Q.proj b * P.proj a)^2 -
      (2*(n:ℝ)⁻¹) • (P.proj a * Q.proj b * P.proj a) +
      ((n:ℝ)⁻¹)^2 • P.proj a := by
  have hpp : P.proj a * P.proj a = P.proj a := (P.isProj a).isIdempotentElem
  have hl : P.proj a * (P.proj a * Q.proj b * P.proj a) =
      P.proj a * Q.proj b * P.proj a := by
    simp only [← mul_assoc, hpp]
  have hr : (P.proj a * Q.proj b * P.proj a) * P.proj a =
      P.proj a * Q.proj b * P.proj a := by
    rw [mul_assoc (P.proj a * Q.proj b), (P.isProj a).isIdempotentElem]
  simp only [pairDefect, pow_two, sub_mul, mul_sub, smul_mul_assoc,
    mul_smul_comm, smul_smul, hl, hr, hpp]
  module

theorem pairDefect_square_sum_le (hn : 0 < n) (P Q : PVM n D) (a : Fin n) :
    (∑ b, (pairDefect P Q a b)^2) ≤ (1-(n:ℝ)⁻¹) • P.proj a := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsum : (∑ b, P.proj a * Q.proj b * P.proj a) = P.proj a := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, Q.complete, mul_one,
      (P.isProj a).isIdempotentElem]
  have hp (b : Fin n) : (pairDefect P Q a b)^2 ≤
      (P.proj a * Q.proj b * P.proj a) -
      ((2*(n:ℝ)⁻¹) • (P.proj a * Q.proj b * P.proj a)) +
      (((n:ℝ)⁻¹)^2 • P.proj a) := by
    rw [pairDefect_square_expand]
    exact add_le_add (sub_le_sub (compression_square_le P Q a b) le_rfl) le_rfl
  have hc : (∑ _b : Fin n, ((n:ℝ)⁻¹)^2 • P.proj a) = (n:ℝ)⁻¹ • P.proj a := by
    rw [← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    field_simp
  have hbound := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.smul_sum, hsum, hc] at hbound
  convert hbound using 1 <;> module

theorem totalRho_lower (P Q R : PVM n D) :
    -totalSigma P Q R ≤ totalRho P Q R := by
  have h1 := anchorRho_lower_oriented P Q R
  have h2 := anchorRho_lower_oriented Q R P
  have h3 := anchorRho_lower_oriented R P Q
  rw [pairSigma_symm Q P] at h1
  rw [pairSigma_symm R Q] at h2
  rw [pairSigma_symm P R] at h3
  unfold totalSigma totalRho
  linarith

end
end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem hermitian_product_energy (X Y : Mat D)
    (hX : IsSelfAdjoint X) (hY : IsSelfAdjoint Y) :
    matTrace (X*Y*star (X*Y)) = matTrace (Y^2*X^2) := by
  unfold matTrace
  congr 1
  simp only [star_mul, hX.star_eq, hY.star_eq, pow_two]
  calc
    _ = Matrix.trace (X*(Y*(Y*X))) := by rw [mul_assoc]
    _ = Matrix.trace (Y*(Y*X)*X) := Matrix.trace_mul_comm X (Y*(Y*X))
    _ = _ := by congr 1; noncomm_ring

def pairMixedEnergy (P Q R : PVM n D) : ℝ :=
  ∑ a, ∑ b, ∑ c, matTrace
    (pairDefect P Q a b * pairDefect P R a c * star (pairDefect P Q a b * pairDefect P R a c))

theorem pairMixedEnergy_bound_right (hn : 0 < n) (P Q R : PVM n D) :
    pairMixedEnergy P Q R ≤ (1-(n:ℝ)⁻¹) * pairSigma P R := by
  have hp (a c : Fin n) :
      (∑ b, matTrace (pairDefect P Q a b * pairDefect P R a c *
        star (pairDefect P Q a b * pairDefect P R a c))) ≤
      (1-(n:ℝ)⁻¹) * matTrace ((pairDefect P R a c)^2) := by
    have h := trace_product_mono (pairDefect_selfAdjoint P R a c).sq_nonneg
      (pairDefect_square_sum_le hn P Q a)
    have hs : (pairDefect P R a c)^2 * P.proj a = (pairDefect P R a c)^2 := by
      rw [pow_two, mul_assoc, pairDefect_right_supported]
    simp only [Matrix.mul_sum, Matrix.mul_smul, hs, Matrix.trace_sum,
      Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
    have he (b : Fin n) : matTrace (pairDefect P Q a b * pairDefect P R a c *
        star (pairDefect P Q a b * pairDefect P R a c)) =
        matTrace ((pairDefect P R a c)^2 * (pairDefect P Q a b)^2) :=
      hermitian_product_energy _ _ (pairDefect_selfAdjoint P Q a b)
        (pairDefect_selfAdjoint P R a c)
    simp_rw [he]
    exact h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun c _ => hp a c))
  simp only [← Finset.mul_sum] at h
  unfold pairMixedEnergy pairSigma
  calc
    _ = ∑ a, ∑ c, ∑ b, matTrace (pairDefect P Q a b * pairDefect P R a c *
        star (pairDefect P Q a b * pairDefect P R a c)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
    _ ≤ _ := h

theorem pairMixedEnergy_symm (P Q R : PVM n D) :
    pairMixedEnergy P Q R = pairMixedEnergy P R Q := by
  unfold pairMixedEnergy
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  rw [hermitian_product_energy _ _ (pairDefect_selfAdjoint P Q a b) (pairDefect_selfAdjoint P R a c),
    hermitian_product_energy _ _ (pairDefect_selfAdjoint P R a c) (pairDefect_selfAdjoint P Q a b)]
  unfold matTrace
  rw [Matrix.trace_mul_comm]

theorem pairMixedEnergy_bound (hn : 0 < n) (P Q R : PVM n D) :
    pairMixedEnergy P Q R ≤
      (1-(n:ℝ)⁻¹) * (pairSigma P Q + pairSigma P R)/2 := by
  have h1 := pairMixedEnergy_bound_right hn P Q R
  have h2 := pairMixedEnergy_bound_right hn P R Q
  rw [← pairMixedEnergy_symm P Q R] at h2
  linarith

end
end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem anchorXi_young_lower (P Q R : PVM n D) (eps : ℝ) (heps : 0 < eps) :
    -(eps * anchorVariance P Q R + pairMixedEnergy P Q R/eps)/2 ≤ anchorXi P Q R := by
  have hp (a b c : Fin n) :
      -(eps * matTrace ((defect P Q R a b c)^2) +
        matTrace (pairDefect P Q a b * pairDefect P R a c *
          star (pairDefect P Q a b * pairDefect P R a c))/eps)/2 ≤
      matTrace (pairDefect P R a c * defect P Q R a b c * pairDefect P Q a b) := by
    have h := trace_young_lower (defect P Q R a b c)
      (pairDefect P Q a b * pairDefect P R a c) (defect_selfAdjoint P Q R a b c) eps heps
    have hc : matTrace (defect P Q R a b c * (pairDefect P Q a b * pairDefect P R a c)) =
        matTrace (pairDefect P R a c * defect P Q R a b c * pairDefect P Q a b) := by
      unfold matTrace
      congr 1
      simpa only [mul_assoc] using (Matrix.trace_mul_cycle
        (defect P Q R a b c) (pairDefect P Q a b) (pairDefect P R a c))
    rwa [hc] at h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun b _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun c _ => hp a b c)))
  simpa only [← Finset.sum_div, Finset.sum_neg_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, anchorVariance, pairMixedEnergy, anchorXi] using h

theorem anchorXi_defect_lower (hn : 0 < n) (P Q R : PVM n D)
    (eps : ℝ) (heps : 0 < eps) :
    -(eps * anchorVariance P Q R +
      ((1-(n:ℝ)⁻¹) * (pairSigma P Q + pairSigma P R)/2)/eps)/2 ≤ anchorXi P Q R := by
  have h1 := anchorXi_young_lower P Q R eps heps
  have h2 := div_le_div_of_nonneg_right (pairMixedEnergy_bound hn P Q R) heps.le
  linarith

theorem totalXi_defect_lower (hn : 0 < n) (P Q R : PVM n D)
    (eps : ℝ) (heps : 0 < eps) :
    -(7*eps*totalVariance P Q R + (7/eps)*(1-(n:ℝ)⁻¹)*totalSigma P Q R) ≤
      14*totalXi P Q R := by
  have h1 := anchorXi_defect_lower hn P Q R eps heps
  have h2 := anchorXi_defect_lower hn Q R P eps heps
  have h3 := anchorXi_defect_lower hn R P Q eps heps
  rw [pairSigma_symm P R] at h1
  rw [pairSigma_symm Q P] at h2
  rw [pairSigma_symm R Q] at h3
  unfold totalVariance totalSigma totalXi
  simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
  nlinarith

theorem aggregate_PVM_defect_lower (hn : 2 ≤ n) (P Q R : PVM n D)
    (x : ℝ) (hx : 0 ≤ x) (hx2 : 81/16 < (n:ℝ)*x^2) :
    3*totalSigma P Q R + (x+2)*totalVariance P Q R/10 ≤
      (2*(n:ℝ)*x^3+(4*(n:ℝ)+10)*x^2+(2*(n:ℝ)+26)*x+22+30/(n:ℝ))*totalSigma P Q R +
      (2*(n:ℝ)*x+4*(n:ℝ)+14)*totalKappa P Q R +
      (x+2)*(totalVariance P Q R+4*totalRho P Q R) + 14*totalXi P Q R := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hep : 0 < 9*(x+2)/70 := by positivity
  have hz := totalXi_defect_lower hn0 P Q R (9*(x+2)/70) hep
  have he : 7*(9*(x+2)/70) = 9*(x+2)/10 := by ring
  have hf : 7/(9*(x+2)/70) = 490/(9*(x+2)) := by field_simp; ring
  rw [he, hf] at hz
  apply FourMeasurementPositivity.aggregate_defect_lower_bound (n:ℝ) x
    (totalSigma P Q R) (totalKappa P Q R) (totalVariance P Q R)
    (totalRho P Q R) (totalXi P Q R) hn' hx hx2
    (totalSigma_nonneg P Q R) (totalVariance_nonneg P Q R)
  · simpa only [div_eq_mul_inv, neg_mul, mul_neg, mul_comm] using totalKappa_lower P Q R
  · exact totalRho_lower P Q R
  · simpa only [one_div] using hz

end
end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
noncomputable section
variable {n D : ℕ}

theorem pairDefect_zero_of_pairSigma_zero (P Q : PVM n D)
    (hs : pairSigma P Q = 0) : ∀ a b, pairDefect P Q a b = 0 := by
  have hnon (a b : Fin n) : 0 ≤ matTrace ((pairDefect P Q a b)^2) := by
    have h := matrix_trace_mono (pairDefect_selfAdjoint P Q a b).sq_nonneg
    simpa only [matTrace, Matrix.trace_zero, Complex.zero_re] using h
  intro a b
  have ha := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ =>
    Finset.sum_nonneg (fun b _ => hnon a b))).mp hs a (Finset.mem_univ _)
  have hb := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hnon a b)).mp ha b (Finset.mem_univ _)
  exact selfAdjoint_eq_zero_of_trace_square _ (pairDefect_selfAdjoint P Q a b) hb

theorem unbiased_of_pairSigma_zero (P Q : PVM n D) (hs : pairSigma P Q = 0) :
    Unbiased P Q := by
  have ht : pairSigma Q P = 0 := by rw [← pairSigma_symm]; exact hs
  exact ⟨fun a b => sub_eq_zero.mp (pairDefect_zero_of_pairSigma_zero P Q hs a b),
    fun a b => sub_eq_zero.mp (pairDefect_zero_of_pairSigma_zero Q P ht b a)⟩

theorem anchor_defect_zero_of_variance_zero (P Q R : PVM n D)
    (hv : anchorVariance P Q R = 0) : ∀ a b c, defect P Q R a b c = 0 := by
  apply defect_eq_zero_of_trace_defectSquares
  simpa only [anchorVariance, matTrace, defectSquares, Matrix.trace_sum, Complex.re_sum] using hv

theorem threeUM_of_zero_aggregate_defects (P Q R : PVM n D)
    (hs : totalSigma P Q R = 0) (hv : totalVariance P Q R = 0) : IsThreeUM P Q R := by
  have hs1 := pairSigma_nonneg P Q
  have hs2 := pairSigma_nonneg Q R
  have hs3 := pairSigma_nonneg R P
  have hv1 := anchorVariance_nonneg P Q R
  have hv2 := anchorVariance_nonneg Q R P
  have hv3 := anchorVariance_nonneg R P Q
  unfold totalSigma at hs
  unfold totalVariance at hv
  refine ⟨unbiased_of_pairSigma_zero P Q (by linarith),
    unbiased_of_pairSigma_zero Q R (by linarith),
    unbiased_of_pairSigma_zero R P (by linarith), ?_⟩
  intro a b c
  exact ⟨anchor_defect_zero_of_variance_zero P Q R (by linarith) a b c,
    anchor_defect_zero_of_variance_zero Q R P (by linarith) b c a,
    anchor_defect_zero_of_variance_zero R P Q (by linarith) c a b⟩

theorem residual_gap_of_selected_le (P Q R T : PVM n D) (hn : 0 < n)
    (lam : ℝ) (hselected : ∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) :
    ∀ abc, (n : ℝ)⁻¹ • (1 : Mat D) ≤ lam • 1 - tripleSum P Q R abc := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  intro abc
  have hdom (e : Fin n) : T.proj e ≤ lam • (1 : Mat D)-tripleSum P Q R abc := by
    simpa only [zero_smul, add_zero] using
      resolvent_dominates_positive_summand (tripleSum P Q R abc) (T.proj e) lam 0
        (tripleSum_nonneg P Q R abc) (T.proj_nonneg e)
        (by simpa only [sub_zero, selectedSum, tripleSum] using hselected abc.1 abc.2.1 abc.2.2 e)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hdom e)
  rw [T.complete, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hs
  have ht := smul_le_smul_of_nonneg_left hs (show (0 : ℝ) ≤ (n : ℝ)⁻¹ by positivity)
  simpa only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn0, one_smul] using ht

end
end FourMeas
end

section
open scoped BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace FourMeas
open MUMSpectral
variable {n D : ℕ}

theorem harmonic_trace_ge_dimension_of_selected_le (P Q R T : PVM n D)
    (hn : 0 < n) (hD : 0 < D) (lam : ℝ)
    (hselected : ∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) :
    (D:ℝ) ≤ matTrace (tripleHarmonicMean P Q R lam) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  by_contra! hlt
  obtain ⟨⟨a,b,c⟩,e,he⟩ := selected_gt_of_harmonic_trace_lt hn hD
    (tripleSum P Q R) T lam (n:ℝ)⁻¹ (inv_pos.mpr hnR)
    (tripleSum_nonneg P Q R) (residual_gap_of_selected_le P Q R T hn lam hselected) hlt
  exact (not_lt_of_ge (hselected a b c e)) he

theorem Phi_nonpos_of_selected_le (P Q R T : PVM n D)
    (hn : 2 ≤ n) (hD : 0 < D) (lam : ℝ) (hlam : LargestRoot n lam)
    (hselected : ∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) :
    Phi P Q R lam ≤ 0 := by
  have hnpos : 0 < n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hnpos
  have hw := FourMeasScalars.omega_positive hn lam hlam
  have hgap := residual_gap_of_selected_le P Q R T hnpos lam hselected
  have hres (abc : Fin n × Fin n × Fin n) :
      (lam • (1:Mat D)-tripleSum P Q R abc).PosDef :=
    posDef_of_scalar_lower (inv_pos.mpr hnR) (hgap abc)
  have hlo := harmonic_trace_ge_dimension_of_selected_le P Q R T hnpos hD lam hselected
  have hhi := Harmonic.harmonic_trace_deficit P Q R (Nat.ne_of_gt hnpos) lam hlam.1 hw.ne' hres
  rw [← Phi_eq_average] at hhi
  have hdiv : Phi P Q R lam/(lam*MUMSpectral.cubic n lam)^2 ≤ 0 := by linarith
  have hh := (div_le_iff₀ (sq_pos_of_ne_zero hw.ne')).mp hdiv
  simpa only [zero_mul] using hh

theorem threeUM_of_quantitative_Phi_and_selected_le (P Q R T : PVM n D)
    (hn : 2 ≤ n) (hD : 0 < D) (lam : ℝ) (hlam : LargestRoot n lam)
    (hquant : 3*totalSigma P Q R + ((lam-1)+2)*totalVariance P Q R/10 ≤
      (n:ℝ)^3*Phi P Q R lam)
    (hselected : ∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) :
    IsThreeUM P Q R := by
  have hPhi := Phi_nonpos_of_selected_le P Q R T hn hD lam hlam hselected
  have hN : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hupper : (n:ℝ)^3*Phi P Q R lam ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hN _) hPhi
  have hs := totalSigma_nonneg P Q R
  have hv := totalVariance_nonneg P Q R
  have hl := (FourMeasScalars.root_bounds hn lam hlam).1
  have hcoeff : 0 < (lam-1)+2 := by linarith
  have hvterm := mul_nonneg hcoeff.le hv
  have hs0 : totalSigma P Q R = 0 := by nlinarith
  have hv0 : totalVariance P Q R = 0 := by nlinarith
  exact threeUM_of_zero_aggregate_defects P Q R hs0 hv0

theorem four_triple_rigidity_of_quantitative_Phi (P Q R T : PVM n D)
    (hn : 2 ≤ n) (hD : 0 < D) (lam : ℝ) (hlam : LargestRoot n lam)
    (hquant : ∀ A B C : PVM n D,
      3*totalSigma A B C + ((lam-1)+2)*totalVariance A B C/10 ≤ (n:ℝ)^3*Phi A B C lam)
    (hselected : ∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) :
    IsThreeUM P Q R ∧ IsThreeUM P Q T ∧ IsThreeUM P R T ∧ IsThreeUM Q R T := by
  refine ⟨threeUM_of_quantitative_Phi_and_selected_le P Q R T hn hD lam hlam (hquant P Q R) hselected,
    threeUM_of_quantitative_Phi_and_selected_le P Q T R hn hD lam hlam (hquant P Q T) ?_,
    threeUM_of_quantitative_Phi_and_selected_le P R T Q hn hD lam hlam (hquant P R T) ?_,
    threeUM_of_quantitative_Phi_and_selected_le Q R T P hn hD lam hlam (hquant Q R T) ?_⟩
  · intro a b c e
    simpa only [selectedSum, add_assoc, add_comm, add_left_comm] using hselected a b e c
  · intro a b c e
    simpa only [selectedSum, add_assoc, add_comm, add_left_comm] using hselected a e b c
  · intro a b c e
    simpa only [selectedSum, add_assoc, add_comm, add_left_comm] using hselected e a b c

end FourMeas
end

section
namespace FourMeasScalars
open MUMSpectral SpectralPolynomialBounds

theorem root_above_one {n : ℕ} (hn : 2 ≤ n) (lam : ℝ)
    (hlam : LargestRoot n lam) : 1 < lam := by
  have hN : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hNe : (n:ℝ) ≠ 0 := by positivity
  obtain ⟨hy,hyb,hysq⟩ := inverse_sqrt_bounds (n:ℝ) hN
  have hr : IsGreatest {t : ℝ | originalQuartic (n:ℝ) t=0} lam := hlam
  have hq : IsGreatest {t : ℝ | q4 (1/Real.sqrt (n:ℝ)) t=0} lam := by
    simpa only [q4_eq_original (n:ℝ) _ _ hNe hysq] using hr
  have h := largest_root_above_test _ lam hy hyb hq
  linarith

end FourMeasScalars
end

section
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open MUMSpectral

namespace FourMeas

theorem quantitative_Phi {n D : ℕ} (hn : 2 ≤ n) (P Q R : PVM n D)
    (lam : ℝ) (hlam : LargestRoot n lam) :
    3*totalSigma P Q R+((lam-1)+2)*totalVariance P Q R/10 ≤
      (n:ℝ)^3*Phi P Q R lam := by
  rw [Phi_eq_defects (by omega) P Q R lam]
  exact aggregate_PVM_defect_lower hn P Q R (lam-1)
    (sub_nonneg.mpr (FourMeasScalars.root_above_one hn lam hlam).le)
    (FourMeasScalars.root_bounds hn lam hlam).2.2

theorem Phi_nonnegative {n D : ℕ} (hn : 2 ≤ n) (P Q R : PVM n D)
    (lam : ℝ) (hlam : LargestRoot n lam) : 0 ≤ Phi P Q R lam := by
  have hq := quantitative_Phi hn P Q R lam hlam
  have hs := totalSigma_nonneg P Q R
  have hv := totalVariance_nonneg P Q R
  have hl := FourMeasScalars.root_above_one hn lam hlam
  have ht : 0 ≤ 3*totalSigma P Q R+((lam-1)+2)*totalVariance P Q R/10 := by positivity
  have hN : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  exact nonneg_of_mul_nonneg_right (ht.trans hq) (pow_pos hN 3)

end FourMeas

theorem four_measurement_arbitrary_rank :
    ∀ (n D : ℕ), 2 ≤ n → 0 < D →
    ∀ (P Q R T : PVM n D) (lam : ℝ), LargestRoot n lam →
      ∃ a b c e : Fin n, lam ≤ ‖selectedSum P Q R T a b c e‖ := by
  intro n D hn hD P Q R T lam hlam
  apply Harmonic.four_pvm_of_nonnegative_polynomial_trace P Q R T hn hD lam
    hlam.1 (FourMeasScalars.omega_positive hn lam hlam).ne'
  rw [← FourMeas.Phi_eq_average]
  exact FourMeas.Phi_nonnegative hn P Q R lam hlam

theorem four_measurement_arbitrary_rank_rigidity :
    ∀ (n D : ℕ), 2 ≤ n → 0 < D →
    ∀ (P Q R T : PVM n D) (lam : ℝ), LargestRoot n lam →
      (∀ a b c e, ‖selectedSum P Q R T a b c e‖ ≤ lam) →
      FourMeas.IsThreeUM P Q R ∧ FourMeas.IsThreeUM P Q T ∧
      FourMeas.IsThreeUM P R T ∧ FourMeas.IsThreeUM Q R T := by
  intro n D hn hD P Q R T lam hlam hselected
  exact FourMeas.four_triple_rigidity_of_quantitative_Phi P Q R T hn hD lam hlam
    (fun A B C => FourMeas.quantitative_Phi hn A B C lam hlam) hselected
end
