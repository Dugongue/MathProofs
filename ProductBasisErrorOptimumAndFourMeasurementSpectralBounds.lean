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

/-!
# Sharp product-basis error and four-measurement selected-sum bounds

For four orthonormal product bases in the fixed tensor decomposition
C^6 = C^2 tensor C^3, the total squared deviation of cross-basis transition
probabilities from 1/6 has exact minimum 2/3, including indirect product bases.
It is attained exactly by direct products of tetrahedral qubit bases and four
mutually unbiased qutrit bases, up to unit phases and permutations within each
basis. An explicit such construction is included.
The sharp mean and worst-pair squared Bengtsson distances are 44/45;
the sharp maximum-pair error and maximum-entry deviation are 1/9 and 1/18.

This quantitatively strengthens the no-four-product-MUB consequence following
Theorem 3 of McNulty and Weigert, "All Mutually Unbiased Product Bases in
Dimension Six", J. Phys. A 45 (2012) 135307, arXiv:1111.3632.
It does not subsume that paper's full classification or its unrestricted-vector
nonextension theorem.

For every n >= 2 and every positive ambient dimension, three pairwise mutually
unbiased n-outcome projective measurements, of arbitrary outcome rank, and any
fourth n-outcome PVM have a selected sum with Euclidean operator norm at least
the largest root of
t^4 - 4*t^3 + 6*(n-1)*t^2/n - 4*(n-1)*(n-2)*t/n^2
  + (n-1)*(n-2)*(n-3)/n^3.
For three ordinary MUBs in dimension six, the selected-sum norm is strictly
greater than that root plus 1/583200, against any fourth six-outcome PVM.

These spectral results extend the bound in Theorem 9 and Appendix D of
Designolle and Farkas, "k-fold unbiased measurements and maximal incompatibility",
arXiv:2609.20728 (2026), to the arbitrary-rank four-measurement subclass
containing a pairwise unbiased triple, with the stated quantitative
dimension-six improvement. They do not settle the unrestricted arbitrary-PVM
conjecture or the existence of four unrestricted MUBs in dimension six.
Equality in the arbitrary-rank bound forces the residual triple's threefold
unbiasedness identities.

The minimizer classification is proved in both directions, with exact
coordinate factorizations, unit phases, and equivalences enumerating all six
tensor products. Every optimal cross-basis entry has absolute deviation 1/18.
Only Mathlib is imported. All intermediate lemmas are proved here.
-/

section


/-! Exact operator definitions for the four-setting selected-sum lower bound.
The norm is the Euclidean operator norm, and the order is the Loewner order.
No moment, positivity-defect, or harmonic inequality is an assumed field. -/

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

/-- The universal four-setting statement, proved below. -/
def FourSettingLowerBound : Prop :=
  ∀ (n D : ℕ), 2 ≤ n → 0 < D →
  ∀ (P Q R T : PVM n D), Unbiased P Q → Unbiased Q R → Unbiased R P →
  ∀ lam : ℝ, LargestRoot n lam →
    ∃ a b c d : Fin n, lam ≤ ‖selectedSum P Q R T a b c d‖

end MUMSpectral



namespace MUMSpectral

section Algebra
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The noncommutative defect-to-cycle identity used before summing outcomes. -/
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

/-- Exact sum-of-squares identity underlying the real-part square estimate. -/
theorem real_part_square_identity (d : A) :
    (d + star d)^2 + (d-star d)*star (d-star d) =
      2 • (d*star d + star d*d) := by
  simp only [star_sub, star_star, two_nsmul]
  noncomm_ring

/-- The three-summand square estimate is an exact sum of three squares. -/
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

/-- Compression by a projection is contractive in the Loewner order. -/
theorem projection_sandwich_le (x q : M) (hq : IsStarProjection q) :
    x*q*star x ≤ x*star x := by
  have h := star_right_conjugate_nonneg hq.one_sub.nonneg x
  apply sub_nonneg.mp
  simpa only [mul_sub, sub_mul, mul_one] using h

/-- Finite orthogonal-output contraction; no commutativity of the x's is assumed. -/
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

/-- The projection-compression step which turns all outcome inequalities into a trace bound. -/
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

/-- A uniform positive lower bound gives the corresponding inverse upper bound. -/
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

/-- Exact second-order resolvent expansion in a noncommutative ring. -/
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

/-- The trace expansion used in the harmonic deficit estimate. -/
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

/-- Algebraic positivity of the resolvent remainder; applicable to B=p(S). -/
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

/-- Trace pairing is monotone in its second positive-semidefinite factor. -/
theorem trace_product_mono {A B C : M} (hA : 0 ≤ A) (hBC : B ≤ C) :
    (Matrix.trace (A*B)).re ≤ (Matrix.trace (A*C)).re := by
  have h := matrix_trace_product_nonneg hA (sub_nonneg.mpr hBC)
  simpa only [mul_sub, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

/-- A lower spectral bound and a quadratic trace bound yield a resolvent deficit. -/
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

/-- A common positive lower bound is preserved by the matrix harmonic mean. -/
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

/-- An exact polynomial remainder identity produces a resolvent minorant. -/
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

/-- A harmonic trace bound forces a selected sum to reach the target norm. -/
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

/-- Both row and column normalization control the Hermitian part of the cyclic sum. -/
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

private theorem trace_defect_square {D : ℕ} (p x : Mat D) (u : ℝ)
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

private theorem sum_defect_zero {n D : ℕ} (hn : 0<n) (P Q R : PVM n D) :
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
    have h := trace_defect_square (P.proj a) (Q.proj b*R.proj c+R.proj c*Q.proj b)
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
    rw [sum_defect_mul_cycle hn P Q R hPQ hQR, sum_defect_zero hn P Q R,
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

namespace MUMPowerReduction
variable {A : Type*} [Ring A] [Algebra ℝ A]
variable (p q r : A) (t : ℝ)
variable (hp : p*p=p) (hq : q*q=q) (hr : r*r=r)
variable (hpq : p*q*p=t • p) (hpr : p*r*p=t • p)
variable (hqp : q*p*q=t • q) (hqr : q*r*q=t • q)
variable (hrp : r*p*r=t • r) (hrq : r*q*r=t • r)

private theorem hpptail (x : A) (ha : p*p=p) : p*(p*x)=p*x := by
  rw [← mul_assoc, ha]

private theorem hqqtail (x : A) (ha : q*q=q) : q*(q*x)=q*x := by
  rw [← mul_assoc, ha]

private theorem hrrtail (x : A) (ha : r*r=r) : r*(r*x)=r*x := by
  rw [← mul_assoc, ha]

private theorem hpqptail (x : A) (ha : p*q*p=t • p) :
    p*(q*(p*x))=t • (p*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hprptail (x : A) (ha : p*r*p=t • p) :
    p*(r*(p*x))=t • (p*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hqpqtail (x : A) (ha : q*p*q=t • q) :
    q*(p*(q*x))=t • (q*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hqrqtail (x : A) (ha : q*r*q=t • q) :
    q*(r*(q*x))=t • (q*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hrprtail (x : A) (ha : r*p*r=t • r) :
    r*(p*(r*x))=t • (r*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

private theorem hrqrtail (x : A) (ha : r*q*r=t • r) :
    r*(q*(r*x))=t • (r*x) := by
  rw [← mul_assoc, ← mul_assoc, ha, smul_mul_assoc]

include hp hq hr hpq hpr hqp hqr hrp hrq

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_1 : (p+q+r)^1 =
    (1 : ℝ) • (p) +
    (1 : ℝ) • (q) +
    (1 : ℝ) • (r) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_2 : (p+q+r)^2 =
    (1 : ℝ) • (p) +
    (1 : ℝ) • (q) +
    (1 : ℝ) • (r) +
    (1 : ℝ) • (p*q) +
    (1 : ℝ) • (p*r) +
    (1 : ℝ) • (q*p) +
    (1 : ℝ) • (q*r) +
    (1 : ℝ) • (r*p) +
    (1 : ℝ) • (r*q) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_3 : (p+q+r)^3 =
    (1+2*t^1 : ℝ) • (p) +
    (1+2*t^1 : ℝ) • (q) +
    (1+2*t^1 : ℝ) • (r) +
    (2 : ℝ) • (p*q) +
    (2 : ℝ) • (p*r) +
    (2 : ℝ) • (q*p) +
    (2 : ℝ) • (q*r) +
    (2 : ℝ) • (r*p) +
    (2 : ℝ) • (r*q) +
    (1 : ℝ) • (p*q*r) +
    (1 : ℝ) • (p*r*q) +
    (1 : ℝ) • (q*p*r) +
    (1 : ℝ) • (q*r*p) +
    (1 : ℝ) • (r*p*q) +
    (1 : ℝ) • (r*q*p) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_4 : (p+q+r)^4 =
    (1+6*t^1 : ℝ) • (p) +
    (1+6*t^1 : ℝ) • (q) +
    (1+6*t^1 : ℝ) • (r) +
    (3+3*t^1 : ℝ) • (p*q) +
    (3+3*t^1 : ℝ) • (p*r) +
    (3+3*t^1 : ℝ) • (q*p) +
    (3+3*t^1 : ℝ) • (q*r) +
    (3+3*t^1 : ℝ) • (r*p) +
    (3+3*t^1 : ℝ) • (r*q) +
    (3 : ℝ) • (p*q*r) +
    (3 : ℝ) • (p*r*q) +
    (3 : ℝ) • (q*p*r) +
    (3 : ℝ) • (q*r*p) +
    (3 : ℝ) • (r*p*q) +
    (3 : ℝ) • (r*q*p) +
    (1 : ℝ) • (p*q*r*p) +
    (1 : ℝ) • (p*r*q*p) +
    (1 : ℝ) • (q*p*r*q) +
    (1 : ℝ) • (q*r*p*q) +
    (1 : ℝ) • (r*p*q*r) +
    (1 : ℝ) • (r*q*p*r) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_5 : (p+q+r)^5 =
    (1+12*t^1+6*t^2 : ℝ) • (p) +
    (1+12*t^1+6*t^2 : ℝ) • (q) +
    (1+12*t^1+6*t^2 : ℝ) • (r) +
    (4+12*t^1 : ℝ) • (p*q) +
    (4+12*t^1 : ℝ) • (p*r) +
    (4+12*t^1 : ℝ) • (q*p) +
    (4+12*t^1 : ℝ) • (q*r) +
    (4+12*t^1 : ℝ) • (r*p) +
    (4+12*t^1 : ℝ) • (r*q) +
    (6+4*t^1 : ℝ) • (p*q*r) +
    (6+4*t^1 : ℝ) • (p*r*q) +
    (6+4*t^1 : ℝ) • (q*p*r) +
    (6+4*t^1 : ℝ) • (q*r*p) +
    (6+4*t^1 : ℝ) • (r*p*q) +
    (6+4*t^1 : ℝ) • (r*q*p) +
    (4 : ℝ) • (p*q*r*p) +
    (4 : ℝ) • (p*r*q*p) +
    (4 : ℝ) • (q*p*r*q) +
    (4 : ℝ) • (q*r*p*q) +
    (4 : ℝ) • (r*p*q*r) +
    (4 : ℝ) • (r*q*p*r) +
    (1 : ℝ) • (p*q*r*p*q) +
    (1 : ℝ) • (p*r*q*p*r) +
    (1 : ℝ) • (q*p*r*q*p) +
    (1 : ℝ) • (q*r*p*q*r) +
    (1 : ℝ) • (r*p*q*r*p) +
    (1 : ℝ) • (r*q*p*r*q) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8000 in
theorem power_6 : (p+q+r)^6 =
    (1+20*t^1+30*t^2 : ℝ) • (p) +
    (1+20*t^1+30*t^2 : ℝ) • (q) +
    (1+20*t^1+30*t^2 : ℝ) • (r) +
    (5+30*t^1+10*t^2 : ℝ) • (p*q) +
    (5+30*t^1+10*t^2 : ℝ) • (p*r) +
    (5+30*t^1+10*t^2 : ℝ) • (q*p) +
    (5+30*t^1+10*t^2 : ℝ) • (q*r) +
    (5+30*t^1+10*t^2 : ℝ) • (r*p) +
    (5+30*t^1+10*t^2 : ℝ) • (r*q) +
    (10+20*t^1 : ℝ) • (p*q*r) +
    (10+20*t^1 : ℝ) • (p*r*q) +
    (10+20*t^1 : ℝ) • (q*p*r) +
    (10+20*t^1 : ℝ) • (q*r*p) +
    (10+20*t^1 : ℝ) • (r*p*q) +
    (10+20*t^1 : ℝ) • (r*q*p) +
    (10+5*t^1 : ℝ) • (p*q*r*p) +
    (10+5*t^1 : ℝ) • (p*r*q*p) +
    (10+5*t^1 : ℝ) • (q*p*r*q) +
    (10+5*t^1 : ℝ) • (q*r*p*q) +
    (10+5*t^1 : ℝ) • (r*p*q*r) +
    (10+5*t^1 : ℝ) • (r*q*p*r) +
    (5 : ℝ) • (p*q*r*p*q) +
    (5 : ℝ) • (p*r*q*p*r) +
    (5 : ℝ) • (q*p*r*q*p) +
    (5 : ℝ) • (q*r*p*q*r) +
    (5 : ℝ) • (r*p*q*r*p) +
    (5 : ℝ) • (r*q*p*r*q) +
    (1 : ℝ) • (p*q*r*p*q*r) +
    (1 : ℝ) • (p*r*q*p*r*q) +
    (1 : ℝ) • (q*p*r*q*p*r) +
    (1 : ℝ) • (q*r*p*q*r*p) +
    (1 : ℝ) • (r*p*q*r*p*q) +
    (1 : ℝ) • (r*q*p*r*q*p) := by
  simp only [pow_succ,
    pow_zero,
    mul_one,
    one_mul,
    add_mul,
    mul_add,
    mul_assoc,
    smul_mul_assoc,
    mul_smul_comm,
    smul_smul,
    hp,
    hq,
    hr,
    hpptail p _ hp,
    hqqtail q _ hq,
    hrrtail r _ hr,
    hpqptail p q t _ hpq,
    show p*(q*p)=t • p by simpa only [mul_assoc] using hpq,
    hprptail p r t _ hpr,
    show p*(r*p)=t • p by simpa only [mul_assoc] using hpr,
    hqpqtail p q t _ hqp,
    show q*(p*q)=t • q by simpa only [mul_assoc] using hqp,
    hqrqtail q r t _ hqr,
    show q*(r*q)=t • q by simpa only [mul_assoc] using hqr,
    hrprtail p r t _ hrp,
    show r*(p*r)=t • r by simpa only [mul_assoc] using hrp,
    hrqrtail q r t _ hrq,
    show r*(q*r)=t • r by simpa only [mul_assoc] using hrq]
  module

end MUMPowerReduction


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

include hP hQ hR in
theorem short4 (hp : ∀ a, P a * P a = P a) :
    sum3 (fun a b c => P a * Q b * R c * P a) = (1:A) := by
  simp only [sum3, ← Finset.sum_mul, ← Finset.mul_sum, hR, mul_one,
    hQ, hp, hP]

include hP hQ hR in
theorem short5 (t : ℝ) (hpq : ∀ a b, P a * Q b * P a = t • P a) :
    sum3 (fun a b c => P a * Q b * R c * P a * Q b) = t • (1:A) := by
  simp only [sum3, ← Finset.sum_mul, ← Finset.mul_sum, hR, mul_one,
    hpq, smul_mul_assoc, ← Finset.smul_sum, hQ, hP]


variable (hp : ∀ a, P a * P a = P a) (hq : ∀ b, Q b * Q b = Q b)
variable (hr : ∀ c, R c * R c = R c) (t : ℝ)
variable (hpq : ∀ a b, P a * Q b * P a = t • P a)
variable (hpr : ∀ a c, P a * R c * P a = t • P a)
variable (hqp : ∀ b a, Q b * P a * Q b = t • Q b)
variable (hqr : ∀ b c, Q b * R c * Q b = t • Q b)
variable (hrp : ∀ c a, R c * P a * R c = t • R c)
variable (hrq : ∀ c b, R c * Q b * R c = t • R c)

include hP hQ hR hp hq hr hpq hpr hqp hqr hrp hrq in
set_option maxHeartbeats 4000000 in
theorem moments :
    sum3 (fun a b c => (P a + Q b + R c)^1) =
      (3*(n:ℝ)^2) • (1:A) ∧
    sum3 (fun a b c => (P a + Q b + R c)^2) =
      (3*(n:ℝ)^2+6*n) • (1:A) ∧
    sum3 (fun a b c => (P a + Q b + R c)^3) =
      (3*(1+2*t)*(n:ℝ)^2+12*n+6) • (1:A) ∧
    sum3 (fun a b c => (P a + Q b + R c)^4) =
      (3*(1+6*t)*(n:ℝ)^2+6*(3+3*t)*n+24) • (1:A) ∧
    sum3 (fun a b c => (P a + Q b + R c)^5) =
      (3*(1+12*t+6*t^2)*(n:ℝ)^2+6*(4+12*t)*n+6*(6+4*t)+24+6*t) • (1:A) ∧
    sum3 (fun a b c => (P a + Q b + R c)^6) =
      (3*(1+20*t+30*t^2)*(n:ℝ)^2+6*(5+30*t+10*t^2)*n+6*(10+20*t)+6*(10+5*t)+30*t) • (1:A) +
      sum3 (fun a b c => P a * Q b * R c * P a * Q b * R c) +
      sum3 (fun a b c => P a * R c * Q b * P a * R c * Q b) +
      sum3 (fun a b c => Q b * P a * R c * Q b * P a * R c) +
      sum3 (fun a b c => Q b * R c * P a * Q b * R c * P a) +
      sum3 (fun a b c => R c * P a * Q b * R c * P a * Q b) +
      sum3 (fun a b c => R c * Q b * P a * R c * Q b * P a) := by
  have w_p : sum3 (fun a b c => P a) = ((n:ℝ)^2) • (1:A) := by
    exact short1 P hP
  have w_q : sum3 (fun a b c => Q b) = ((n:ℝ)^2) • (1:A) := by
    have hw := short1 Q hQ
    rw [← sum3_bac (fun a b c => Q a)] at hw
    exact hw
  have w_r : sum3 (fun a b c => R c) = ((n:ℝ)^2) • (1:A) := by
    have hw := short1 R hR
    rw [← sum3_cab (fun a b c => R a)] at hw
    exact hw
  have w_pq : sum3 (fun a b c => P a * Q b) = (n:ℝ) • (1:A) := by
    exact short2 P Q hP hQ
  have w_pr : sum3 (fun a b c => P a * R c) = (n:ℝ) • (1:A) := by
    have hw := short2 P R hP hR
    rw [← sum3_acb (fun a b c => P a * R b)] at hw
    exact hw
  have w_qp : sum3 (fun a b c => Q b * P a) = (n:ℝ) • (1:A) := by
    have hw := short2 Q P hQ hP
    rw [← sum3_bac (fun a b c => Q a * P b)] at hw
    exact hw
  have w_qr : sum3 (fun a b c => Q b * R c) = (n:ℝ) • (1:A) := by
    have hw := short2 Q R hQ hR
    rw [← sum3_bca (fun a b c => Q a * R b)] at hw
    exact hw
  have w_rp : sum3 (fun a b c => R c * P a) = (n:ℝ) • (1:A) := by
    have hw := short2 R P hR hP
    rw [← sum3_cab (fun a b c => R a * P b)] at hw
    exact hw
  have w_rq : sum3 (fun a b c => R c * Q b) = (n:ℝ) • (1:A) := by
    have hw := short2 R Q hR hQ
    rw [← sum3_cba (fun a b c => R a * Q b)] at hw
    exact hw
  have w_pqr : sum3 (fun a b c => P a * Q b * R c) = (1:A) := by
    exact short3 P Q R hP hQ hR
  have w_prq : sum3 (fun a b c => P a * R c * Q b) = (1:A) := by
    have hw := short3 P R Q hP hR hQ
    rw [← sum3_acb (fun a b c => P a * R b * Q c)] at hw
    exact hw
  have w_qpr : sum3 (fun a b c => Q b * P a * R c) = (1:A) := by
    have hw := short3 Q P R hQ hP hR
    rw [← sum3_bac (fun a b c => Q a * P b * R c)] at hw
    exact hw
  have w_qrp : sum3 (fun a b c => Q b * R c * P a) = (1:A) := by
    have hw := short3 Q R P hQ hR hP
    rw [← sum3_bca (fun a b c => Q a * R b * P c)] at hw
    exact hw
  have w_rpq : sum3 (fun a b c => R c * P a * Q b) = (1:A) := by
    have hw := short3 R P Q hR hP hQ
    rw [← sum3_cab (fun a b c => R a * P b * Q c)] at hw
    exact hw
  have w_rqp : sum3 (fun a b c => R c * Q b * P a) = (1:A) := by
    have hw := short3 R Q P hR hQ hP
    rw [← sum3_cba (fun a b c => R a * Q b * P c)] at hw
    exact hw
  have w_pqrp : sum3 (fun a b c => P a * Q b * R c * P a) = (1:A) := by
    exact short4 P Q R hP hQ hR hp
  have w_prqp : sum3 (fun a b c => P a * R c * Q b * P a) = (1:A) := by
    have hw := short4 P R Q hP hR hQ hp
    rw [← sum3_acb (fun a b c => P a * R b * Q c * P a)] at hw
    exact hw
  have w_qprq : sum3 (fun a b c => Q b * P a * R c * Q b) = (1:A) := by
    have hw := short4 Q P R hQ hP hR hq
    rw [← sum3_bac (fun a b c => Q a * P b * R c * Q a)] at hw
    exact hw
  have w_qrpq : sum3 (fun a b c => Q b * R c * P a * Q b) = (1:A) := by
    have hw := short4 Q R P hQ hR hP hq
    rw [← sum3_bca (fun a b c => Q a * R b * P c * Q a)] at hw
    exact hw
  have w_rpqr : sum3 (fun a b c => R c * P a * Q b * R c) = (1:A) := by
    have hw := short4 R P Q hR hP hQ hr
    rw [← sum3_cab (fun a b c => R a * P b * Q c * R a)] at hw
    exact hw
  have w_rqpr : sum3 (fun a b c => R c * Q b * P a * R c) = (1:A) := by
    have hw := short4 R Q P hR hQ hP hr
    rw [← sum3_cba (fun a b c => R a * Q b * P c * R a)] at hw
    exact hw
  have w_pqrpq : sum3 (fun a b c => P a * Q b * R c * P a * Q b) = t • (1:A) := by
    exact short5 P Q R hP hQ hR t hpq
  have w_prqpr : sum3 (fun a b c => P a * R c * Q b * P a * R c) = t • (1:A) := by
    have hw := short5 P R Q hP hR hQ t hpr
    rw [← sum3_acb (fun a b c => P a * R b * Q c * P a * R b)] at hw
    exact hw
  have w_qprqp : sum3 (fun a b c => Q b * P a * R c * Q b * P a) = t • (1:A) := by
    have hw := short5 Q P R hQ hP hR t hqp
    rw [← sum3_bac (fun a b c => Q a * P b * R c * Q a * P b)] at hw
    exact hw
  have w_qrpqr : sum3 (fun a b c => Q b * R c * P a * Q b * R c) = t • (1:A) := by
    have hw := short5 Q R P hQ hR hP t hqr
    rw [← sum3_bca (fun a b c => Q a * R b * P c * Q a * R b)] at hw
    exact hw
  have w_rpqrp : sum3 (fun a b c => R c * P a * Q b * R c * P a) = t • (1:A) := by
    have hw := short5 R P Q hR hP hQ t hrp
    rw [← sum3_cab (fun a b c => R a * P b * Q c * R a * P b)] at hw
    exact hw
  have w_rqprq : sum3 (fun a b c => R c * Q b * P a * R c * Q b) = t • (1:A) := by
    have hw := short5 R Q P hR hQ hP t hrq
    rw [← sum3_cba (fun a b c => R a * Q b * P c * R a * Q b)] at hw
    exact hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have heq : (fun a b c => (P a + Q b + R c)^1) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_1 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module
  · have heq : (fun a b c => (P a + Q b + R c)^2) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_2 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module
  · have heq : (fun a b c => (P a + Q b + R c)^3) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_3 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module
  · have heq : (fun a b c => (P a + Q b + R c)^4) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_4 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module
  · have heq : (fun a b c => (P a + Q b + R c)^5) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_5 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module
  · have heq : (fun a b c => (P a + Q b + R c)^6) = _ := funext fun a => funext fun b => funext fun c =>
      MUMPowerReduction.power_6 (P a) (Q b) (R c) t (hp a) (hq b) (hr c)
        (hpq a b) (hpr a c) (hqp b a) (hqr b c) (hrp c a) (hrq c b)
    rw [heq]
    simp only [sum3_add, sum3_smul, w_p, w_q, w_r, w_pq, w_pr, w_qp, w_qr, w_rp, w_rq, w_pqr, w_prq, w_qpr, w_qrp, w_rpq, w_rqp, w_pqrp, w_prqp, w_qprq, w_qrpq, w_rpqr, w_rqpr, w_pqrpq, w_prqpr, w_qprqp, w_qrpqr, w_rpqrp, w_rqprq]
    module

end MUMMoments



namespace MUMSpectral
open MUMMoments
variable {n D : ℕ}
noncomputable def sixCycles (P Q R : PVM n D) : Mat D :=
  sum3 (fun a b c => P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c) +
  sum3 (fun a b c => P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b) +
  sum3 (fun a b c => Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c) +
  sum3 (fun a b c => Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a) +
  sum3 (fun a b c => R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b) +
  sum3 (fun a b c => R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a)

theorem sixCycles_eq (P Q R : PVM n D) :
    sixCycles P Q R = cycleDefect P Q R + (6*((2-(n:ℝ))/(n:ℝ)^2)) • (1:Mat D) := by
  have hstarP : ∀ a, star (P.proj a) = P.proj a := fun a => (P.isProj a).isSelfAdjoint.star_eq
  have hstarQ : ∀ b, star (Q.proj b) = Q.proj b := fun b => (Q.isProj b).isSelfAdjoint.star_eq
  have hstarR : ∀ c, star (R.proj c) = R.proj c := fun c => (R.isProj c).isSelfAdjoint.star_eq
  have hq : sum3 (fun a b c => Q.proj b * R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a) =
      cycle Q R P := sum3_bca _
  have hr : sum3 (fun a b c => R.proj c * P.proj a * Q.proj b * R.proj c * P.proj a * Q.proj b) =
      cycle R P Q := sum3_cab _
  have hqs := congrArg star hq
  have hrs := congrArg star hr
  simp only [sum3, star_sum, star_mul, hstarP, hstarQ, hstarR] at hqs hrs
  simp only [← mul_assoc] at hqs hrs
  have hps : sum3 (fun a b c => R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a) =
      star (cycle P Q R) := by
    simp only [sum3, cycle, star_sum, star_mul, hstarP, hstarQ, hstarR, mul_assoc]
  unfold sixCycles
  rw [hq, hr, hps]
  change _ = _
  rw [show sum3 (fun a b c => P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c * Q.proj b) =
    star (cycle Q R P) from hqs]
  rw [show sum3 (fun a b c => Q.proj b * P.proj a * R.proj c * Q.proj b * P.proj a * R.proj c) =
    star (cycle R P Q) from hrs]
  change cycle P Q R + star (cycle Q R P) + star (cycle R P Q) +
    cycle Q R P + cycle R P Q + star (cycle P Q R) = _
  simp only [cycleDefect, centeredCycle, star_sub, star_smul, star_one, star_trivial]
  module

theorem raw_moments (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P) :
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^1) = (3*(n:ℝ)^2) • (1:Mat D) ∧
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^2) = (3*(n:ℝ)^2+6*n) • (1:Mat D) ∧
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^3) =
      (3*(1+2*(n:ℝ)⁻¹)*(n:ℝ)^2+12*n+6) • (1:Mat D) ∧
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^4) =
      (3*(1+6*(n:ℝ)⁻¹)*(n:ℝ)^2+6*(3+3*(n:ℝ)⁻¹)*n+24) • (1:Mat D) ∧
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^5) =
      (3*(1+12*(n:ℝ)⁻¹+6*((n:ℝ)⁻¹)^2)*(n:ℝ)^2+6*(4+12*(n:ℝ)⁻¹)*n+
      6*(6+4*(n:ℝ)⁻¹)+24+6*(n:ℝ)⁻¹) • (1:Mat D) ∧
    sum3 (fun a b c => (P.proj a + Q.proj b + R.proj c)^6) =
      (3*(1+20*(n:ℝ)⁻¹+30*((n:ℝ)⁻¹)^2)*(n:ℝ)^2+
      6*(5+30*(n:ℝ)⁻¹+10*((n:ℝ)⁻¹)^2)*n+
      6*(10+20*(n:ℝ)⁻¹)+6*(10+5*(n:ℝ)⁻¹)+30*(n:ℝ)⁻¹) • (1:Mat D) +
      sixCycles P Q R := by
  have h := MUMMoments.moments P.proj Q.proj R.proj P.complete Q.complete R.complete
    (fun a => (P.isProj a).isIdempotentElem.eq)
    (fun b => (Q.isProj b).isIdempotentElem.eq)
    (fun c => (R.isProj c).isIdempotentElem.eq) (n:ℝ)⁻¹
    hPQ.1 (fun a c => hRP.2 c a) (fun b a => hPQ.2 a b)
    hQR.1 hRP.1 (fun c b => hQR.2 b c)
  simpa only [sixCycles, add_assoc] using h
end MUMSpectral


namespace MUMInterpolation
variable {A : Type*} [Ring A] [Algebra ℝ A]
noncomputable def h0 (a b l : ℝ) : ℝ := (b^2) + (-2*a*b)*l^1 + (a^2+6*b)*l^2 + (-6*a-2*b)*l^3 + (9+2*a)*l^4 + (-6)*l^5 + (1)*l^6
noncomputable def h1 (a b l : ℝ) : ℝ := (-2*a*b) + (a^2+6*b)*l^1 + (-6*a-2*b)*l^2 + (9+2*a)*l^3 + (-6)*l^4 + (1)*l^5
noncomputable def h2 (a b l : ℝ) : ℝ := (a^2+6*b) + (-6*a-2*b)*l^1 + (9+2*a)*l^2 + (-6)*l^3 + (1)*l^4
noncomputable def h3 (a b l : ℝ) : ℝ := (-6*a-2*b) + (9+2*a)*l^1 + (-6)*l^2 + (1)*l^3
noncomputable def h4 (a b l : ℝ) : ℝ := (9+2*a) + (-6)*l^1 + (1)*l^2
noncomputable def h5 (a b l : ℝ) : ℝ := (-6) + (1)*l^1
noncomputable def h6 (a b l : ℝ) : ℝ := (1)
noncomputable def numerator (a b l : ℝ) (S : A) : A :=
  h0 a b l • (1:A) + h1 a b l • S + h2 a b l • S^2 +
  h3 a b l • S^3 + h4 a b l • S^4 + h5 a b l • S^5 + h6 a b l • S^6

noncomputable def cubicMatrix (a b : ℝ) (S : A) : A := S^3 - (3:ℝ) • S^2 + a • S - b • (1:A)

set_option maxHeartbeats 4000000 in
theorem numerator_identity (a b l : ℝ) (S : A) :
    (l • (1:A) - S) * numerator a b l S =
      (l*(l^3-3*l^2+a*l-b)^2) • (1:A) - S * (cubicMatrix a b S)^2 := by
  simp only [numerator, cubicMatrix, h0, h1, h2, h3, h4, h5, h6,
    pow_succ, pow_zero, mul_one, one_mul, mul_add, add_mul, mul_sub, sub_mul,
    mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
  module

noncomputable def cubic (N l : ℝ) : ℝ :=
  l^3 - 3*l^2 + (3*(N-1)/N)*l - (N-1)*(N-2)/N^2
noncomputable def quartic (N l : ℝ) : ℝ :=
  l^4 - 4*l^3 + (6*(N-1)/N)*l^2 - (4*(N-1)*(N-2)/N^2)*l +
    (N-1)*(N-2)*(N-3)/N^3

set_option maxHeartbeats 4000000 in
theorem scalar_average_identity (N l : ℝ) (hN : N ≠ 0) :
    h0 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l * N^3 +
    h1 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l * (3*N^2) +
    h2 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l * (3*N^2+6*N) +
    h3 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l * (3*(1+2*N⁻¹)*N^2+12*N+6) +
    h4 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l * (3*(1+6*N⁻¹)*N^2+6*(3+3*N⁻¹)*N+24) +
    h5 (3*(N-1)/N) ((N-1)*(N-2)/N^2) l *
      (3*(1+12*N⁻¹+6*(N⁻¹)^2)*N^2+6*(4+12*N⁻¹)*N+6*(6+4*N⁻¹)+24+6*N⁻¹) +
    (3*(1+20*N⁻¹+30*(N⁻¹)^2)*N^2+6*(5+30*N⁻¹+10*(N⁻¹)^2)*N+
      6*(10+20*N⁻¹)+6*(10+5*N⁻¹)+30*N⁻¹) + 6*((2-N)/N^2) =
      N^3 * (l * (cubic N l)^2 - cubic N l * quartic N l) := by
  simp only [h0, h1, h2, h3, h4, h5, cubic, quartic]
  field_simp [hN]
  <;> ring

end MUMInterpolation



namespace MUMSpectral
open MUMMoments
variable {n D : ℕ}

theorem raw_numerator_average (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (hn : (n:ℝ) ≠ 0) (l : ℝ) :
    sum3 (fun a b c => MUMInterpolation.numerator
      (3*((n:ℝ)-1)/(n:ℝ)) (((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2)
      l (P.proj a + Q.proj b + R.proj c)) =
      ((n:ℝ)^3 * (l * (cubic n l)^2 - cubic n l * quartic n l)) • (1:Mat D) +
      cycleDefect P Q R := by
  obtain ⟨hm1, hm2, hm3, hm4, hm5, hm6⟩ := raw_moments P Q R hPQ hQR hRP
  simp only [pow_one] at hm1
  have hm0 : sum3 (fun (_ _ _ : Fin n) => (1:Mat D)) = ((n:ℝ)^3) • (1:Mat D) := by
    simp only [sum3, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    ring
  change _ = ((n:ℝ)^3 * (l * (MUMInterpolation.cubic (n:ℝ) l)^2 -
    MUMInterpolation.cubic (n:ℝ) l * MUMInterpolation.quartic (n:ℝ) l)) • (1:Mat D) + _
  rw [← MUMInterpolation.scalar_average_identity (n:ℝ) l hn]
  simp only [MUMInterpolation.numerator, sum3_add, sum3_smul, hm0, hm1, hm2, hm3,
    hm4, hm5, hm6, MUMInterpolation.h6, one_smul, sixCycles_eq]
  module

noncomputable def interpolatingMatrix (n : ℕ) (l : ℝ) (S : Mat D) : Mat D :=
  (l * (cubic n l)^2)⁻¹ • MUMInterpolation.numerator
    (3*((n:ℝ)-1)/(n:ℝ)) (((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2) l S

theorem interpolating_average (P Q R : PVM n D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (hn : (n:ℝ) ≠ 0) (l : ℝ) (hw : l*(cubic n l)^2 ≠ 0)
    (hroot : quartic n l = 0) :
    ((n:ℝ)^3)⁻¹ • sum3 (fun a b c =>
      interpolatingMatrix n l (P.proj a + Q.proj b + R.proj c)) =
      (1:Mat D) + (1/((n:ℝ)^3*l*(cubic n l)^2)) • cycleDefect P Q R := by
  simp only [interpolatingMatrix, sum3_smul,
    raw_numerator_average P Q R hPQ hQR hRP hn l, hroot, mul_zero, sub_zero,
    smul_add, smul_smul]
  have hc : ((n:ℝ)^3)⁻¹ * ((l*(cubic n l)^2)⁻¹ * ((n:ℝ)^3 * (l*(cubic n l)^2))) = 1 := by
    calc
      _ = (((n:ℝ)^3)⁻¹ * (n:ℝ)^3) * ((l*(cubic n l)^2)⁻¹ * (l*(cubic n l)^2)) := by ring
      _ = 1 := by rw [inv_mul_cancel₀ (pow_ne_zero 3 hn), inv_mul_cancel₀ hw, one_mul]
  have hc' : ((n:ℝ)^3)⁻¹ * (l*(cubic n l)^2)⁻¹ =
      1/((n:ℝ)^3*l*(cubic n l)^2) := by
    simp only [one_div, mul_inv_rev]
    ring
  rw [hc, one_smul, hc']

theorem interpolating_identity (n : ℕ) (l : ℝ) (S : Mat D)
    (hw : l*(cubic n l)^2 ≠ 0) :
    (l • (1:Mat D) - S) * interpolatingMatrix n l S =
      (1:Mat D) - (l*(cubic n l)^2)⁻¹ •
        (S * (MUMInterpolation.cubicMatrix
          (3*((n:ℝ)-1)/(n:ℝ)) (((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2) S)^2) := by
  unfold interpolatingMatrix
  rw [mul_smul_comm, MUMInterpolation.numerator_identity]
  change (l*(cubic n l)^2)⁻¹ •
    ((l*(cubic n l)^2) • (1:Mat D) - _) = _
  rw [smul_sub, smul_smul, inv_mul_cancel₀ hw, one_smul]
end MUMSpectral


/-! Polynomial estimates used in the four-measurement spectral bound.
The parameter y is 1/sqrt(n); no operator inequality is assumed here. -/
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

theorem centeredCycle_contraction (P Q R : PVM n D) (hn : 0<n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    centeredCycle P Q R*star (centeredCycle P Q R) ≤ defectSquares P Q R := by
  rw [← contractedDefect_eq_centeredCycle P Q R hn hPQ hQR]
  exact contractedDefect_bound P Q R

theorem cycleDefect_selfAdjoint (P Q R : PVM n D) : IsSelfAdjoint (cycleDefect P Q R) := by
  change star (cycleDefect P Q R)=cycleDefect P Q R
  simp only [cycleDefect, star_add, star_star]
  abel

theorem cycleDefect_trace_square (P Q R : PVM n D) (hn : 0<n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P) :
    matTrace ((cycleDefect P Q R)^2) ≤ 12*matTrace (cycleDefect P Q R) := by
  have h := trace_three_realparts_square_le
    (centeredCycle P Q R) (centeredCycle Q R P) (centeredCycle R P Q)
    (defectSquares P Q R) (defectSquares Q R P) (defectSquares R P Q)
    (centeredCycle_contraction P Q R hn hPQ hQR)
    (centeredCycle_contraction Q R P hn hQR hRP)
    (centeredCycle_contraction R P Q hn hRP hPQ)
  change _ ≤ 12*(matTrace (defectSquares P Q R)+matTrace (defectSquares Q R P)+
    matTrace (defectSquares R P Q)) at h
  rw [trace_defectSquares_centeredCycle hn P Q R hPQ hQR,
    trace_defectSquares_centeredCycle hn Q R P hQR hRP,
    trace_defectSquares_centeredCycle hn R P Q hRP hPQ] at h
  simpa only [matTrace, cycleDefect, Matrix.trace_add, Complex.add_re, add_assoc] using h

theorem cycleDefect_trace_nonneg (P Q R : PVM n D) (hn : 0<n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P) :
    0 ≤ matTrace (cycleDefect P Q R) := by
  have h1 := cycleDefect_trace_square P Q R hn hPQ hQR hRP
  have h2 := matrix_trace_mono (cycleDefect_selfAdjoint P Q R).sq_nonneg
  simp only [Matrix.trace_zero, Complex.zero_re] at h2
  change 0 ≤ matTrace ((cycleDefect P Q R)^2) at h2
  linarith

theorem cycleDefect_lower_six (P Q R : PVM n D) (hn : 2≤n) :
    -((6:ℝ) • (1:M)) ≤ cycleDefect P Q R := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hc : 6*(1+(2-(n:ℝ))/(n:ℝ)^2) ≤ 6 := by
    have hh : (2-(n:ℝ))/(n:ℝ)^2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by linarith) (sq_nonneg _)
    linarith
  have hi : (0:M) ≤ 1 := zero_le_one
  have hle := smul_le_smul_of_nonneg_right hc hi
  exact (neg_le_neg hle).trans (cycleDefect_lower_exact P Q R)

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

theorem cycleKappa_bounds (hn : 2≤n) (lam : ℝ) (hlam : LargestRoot n lam) :
    0 < cycleKappa n lam ∧ cycleKappa n lam < 1/18 := by
  have h := SpectralPolynomialBounds.original_root_estimates (n:ℝ) lam
    (by exact_mod_cast hn) hlam
  change _ ∧ 0 < cycleKappa n lam ∧ cycleKappa n lam < (4096:ℝ)/88209 at h
  exact ⟨h.2.1, by linarith [h.2.2]⟩

theorem harmonic_trace_deficit (P Q R : PVM n D) (hn : 2≤n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (hres : ∀ abc, (lam • (1:M)-tripleSum P Q R abc).PosDef) :
    matTrace (tripleHarmonicMean P Q R lam) ≤ (D:ℝ)-
      cycleKappa n lam*(1-12*cycleKappa n lam/(1-6*cycleKappa n lam))*
        matTrace (cycleDefect P Q R) := by
  have hnpos : 0<n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hnpos
  obtain ⟨hkpos,hkbound⟩ := cycleKappa_bounds hn lam hlam
  let k := cycleKappa n lam
  let F := cycleDefect P Q R
  let X : M := 1+k • F
  have hg : 0 < 1-k*6 := by dsimp [k]; linarith
  have hw : 0 < lam*(cubic n lam)^2 := by
    have hd := (one_div_pos.mp hkpos)
    change 0 < (n:ℝ)^3*lam*(cubic n lam)^2 at hd
    rw [mul_assoc] at hd
    exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hnpos) 3)).mp hd
  have hxlower : (1-k*6) • (1:M) ≤ X := by
    have h := smul_le_smul_of_nonneg_left (cycleDefect_lower_six P Q R hn) hkpos.le
    change k • (-((6:ℝ) • (1:M))) ≤ k • F at h
    have hh := add_le_add (le_refl (1:M)) h
    convert hh using 1 <;> (try dsimp [X]) <;> module
  have hX := posDef_of_scalar_lower hg hxlower
  have hpoint (abc : Fin n × (Fin n × Fin n)) :
      interpolatingMatrix n lam (tripleSum P Q R abc) ≤
        (lam • (1:M)-tripleSum P Q R abc)⁻¹ := by
    let S := tripleSum P Q R abc
    let B := MUMInterpolation.cubicMatrix (3*((n:ℝ)-1)/(n:ℝ))
      (((n:ℝ)-1)*((n:ℝ)-2)/(n:ℝ)^2) S
    have hS : 0 ≤ S := tripleSum_nonneg P Q R abc
    have hB : IsSelfAdjoint B := by
      change star B=B
      simp only [B, MUMInterpolation.cubicMatrix, star_sub, star_add, star_smul,
        star_pow, star_trivial, star_one, hS.isSelfAdjoint.star_eq]
    have hBS : Commute B S := by
      change B*S=S*B
      simp only [B, MUMInterpolation.cubicMatrix, mul_sub, sub_mul, mul_add, add_mul,
        mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
      noncomm_ring
    exact resolvent_polynomial_minorant S B (interpolatingMatrix n lam S) lam _
      hS hB hBS (hres abc) hw (interpolating_identity n lam S hw.ne')
  have havg : matrixAverage (fun abc => interpolatingMatrix n lam (tripleSum P Q R abc))=X := by
    have h := interpolating_average P Q R hPQ hQR hRP hn0 lam hw.ne' hlam.1
    have hn3 : (n:ℝ)*((n:ℝ)*(n:ℝ))=(n:ℝ)^3 := by ring
    simpa only [matrixAverage, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      hn3, Fintype.sum_prod_type, tripleSum, MUMMoments.sum3, X, k, F, cycleKappa] using h
  have hmean := matrixAverage_posDef (fun abc => (lam • (1:M)-tripleSum P Q R abc)⁻¹)
    (fun abc => (hres abc).inv)
  have horder := matrixAverage_mono hpoint
  rw [havg] at horder
  have hupper := matrix_trace_mono (matrix_inverse_antitone hX hmean horder)
  have hdef := inverse_trace_deficit F k 6 12 (cycleDefect_selfAdjoint P Q R)
    hkpos.le hg (cycleDefect_lower_six P Q R hn)
    (cycleDefect_trace_square P Q R hnpos hPQ hQR hRP)
  change matTrace (tripleHarmonicMean P Q R lam) ≤ matTrace X⁻¹ at hupper
  have hfinal := hupper.trans hdef
  simpa only [k, F, matTrace, mul_comm (cycleKappa n lam) 6] using hfinal

theorem harmonic_trace_le_dimension (P Q R : PVM n D) (hn : 2≤n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (hres : ∀ abc, (lam • (1:M)-tripleSum P Q R abc).PosDef) :
    matTrace (tripleHarmonicMean P Q R lam) ≤ (D:ℝ) := by
  obtain ⟨hkpos,hkbound⟩ := cycleKappa_bounds hn lam hlam
  have hg : 0 < 1-6*cycleKappa n lam := by linarith
  have hfrac : 12*cycleKappa n lam/(1-6*cycleKappa n lam) ≤ 1 :=
    (div_le_one hg).mpr (by linarith)
  have hprod : 0 ≤ cycleKappa n lam*(1-12*cycleKappa n lam/(1-6*cycleKappa n lam))*
      matTrace (cycleDefect P Q R) := mul_nonneg
    (mul_nonneg hkpos.le (sub_nonneg.mpr hfrac))
    (cycleDefect_trace_nonneg P Q R (by omega) hPQ hQR hRP)
  exact (harmonic_trace_deficit P Q R hn hPQ hQR hRP lam hlam hres).trans
    (sub_le_self _ hprod)

/-- Three pairwise unbiased projective measurements force the four-setting bound
against every fourth projective measurement, in arbitrary finite rank. -/
theorem four_setting_lower_bound (P Q R T : PVM n D) (hn : 2≤n) (hD : 0<D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam) :
    ∃ a b c d : Fin n, lam ≤ ‖selectedSum P Q R T a b c d‖ := by
  have hnpos : 0<n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  obtain ⟨⟨a,b,c⟩,d,h⟩ := selected_norm_of_harmonic_trace hnpos hD
    (tripleSum P Q R) T lam (tripleSum_nonneg P Q R)
    (harmonic_trace_le_dimension P Q R hn hPQ hQR hRP lam hlam)
  exact ⟨a,b,c,d,h⟩

theorem fourSettingLowerBound : FourSettingLowerBound := by
  intro n D hn hD P Q R T hPQ hQR hRP lam hlam
  exact four_setting_lower_bound P Q R T hn hD hPQ hQR hRP lam hlam

theorem exists_largestRoot (hn : 2≤n) : ∃ lam : ℝ, LargestRoot n lam :=
  SpectralPolynomialBounds.original_exists_largest_root (n:ℝ) (by exact_mod_cast hn)

end MUMSpectral


namespace SixPhaseGap

open scoped BigOperators ComplexConjugate Matrix.Norms.Frobenius
open Matrix

noncomputable section

theorem frobenius_sq {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ‖A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp_rw [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt]
  positivity

theorem frobenius_sq_trace {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℂ) : ‖A‖ ^ 2 = (Matrix.trace (A * Aᴴ)).re := by
  rw [frobenius_sq]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    map_sum, Complex.mul_conj, Complex.ofReal_re]
  simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

theorem frobenius_scaled_unitary_right {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (Z : Matrix n n ℂ)
    (hZ : Z * Zᴴ = (6 : ℂ) • (1 : Matrix n n ℂ)) :
    ‖A * Z‖ ^ 2 = 6 * ‖A‖ ^ 2 := by
  rw [frobenius_sq_trace, frobenius_sq_trace]
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Z,
    hZ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.trace_smul]
  simp

theorem sign_six_gap (a b c d e f : ℝ)
    (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
    (hc : c=1 ∨ c= -1) (hd : d=1 ∨ d= -1)
    (he : e=1 ∨ e= -1) (hf : f=1 ∨ f= -1) :
    (2/3:ℝ)^2 ≤ (1+(5/6:ℝ)*(a+b+c+d+e+f))^2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl <;>
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;> norm_num

theorem scaled_unitary_reverse {n : Type*} [Fintype n] [DecidableEq n]
    (Z : Matrix n n ℂ) (hZ : Z * Zᴴ = (6:ℂ) • (1 : Matrix n n ℂ)) :
    Zᴴ * Z = (6:ℂ) • (1 : Matrix n n ℂ) := by
  have h : Z * ((1/6:ℂ) • Zᴴ) = 1 := by
    rw [Matrix.mul_smul, hZ, smul_smul]
    norm_num
  have h' := mul_eq_one_comm.mp h
  have h'' := congrArg (fun A : Matrix n n ℂ => (6:ℂ) • A) h'
  simpa [Matrix.smul_mul, smul_smul] using h''

theorem frobenius_scaled_unitary_right_norm {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] (A : Matrix m n ℂ) (Z : Matrix n n ℂ)
    (hZ : Z * Zᴴ = (6:ℂ) • (1 : Matrix n n ℂ)) :
    ‖A * Z‖ = Real.sqrt 6 * ‖A‖ := by
  have h := frobenius_scaled_unitary_right A Z hZ
  have hsq : (Real.sqrt (6:ℝ))^2=6 := Real.sq_sqrt (by norm_num)
  have ht : (Real.sqrt (6:ℝ)*‖A‖)^2=6*‖A‖^2 := by rw [mul_pow, hsq]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp (h.trans ht.symm)

theorem gram_perturbation {n : Type*} [Fintype n] [DecidableEq n]
    (Z W : Matrix n n ℂ) (hZ : Z * Zᴴ = (6:ℂ) • (1 : Matrix n n ℂ)) :
    ‖W * Wᴴ - Z * Zᴴ‖ ≤
      2 * Real.sqrt 6 * ‖W-Z‖ + ‖W-Z‖^2 := by
  let D := W-Z
  have hr : ‖D * Zᴴ‖ = Real.sqrt 6 * ‖D‖ :=
    frobenius_scaled_unitary_right_norm D Zᴴ (by
      simpa only [Matrix.conjTranspose_conjTranspose] using scaled_unitary_reverse Z hZ)
  have hl : ‖Z * Dᴴ‖ = Real.sqrt 6 * ‖D‖ := by
    rw [← Matrix.frobenius_norm_conjTranspose (Z * Dᴴ)]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hr
  have hid : W * Wᴴ - Z * Zᴴ = D * Zᴴ + Z * Dᴴ + D * Dᴴ := by
    dsimp [D]
    rw [Matrix.conjTranspose_sub]
    noncomm_ring
  rw [hid]
  calc
    ‖D * Zᴴ + Z * Dᴴ + D * Dᴴ‖ ≤
        ‖D * Zᴴ‖ + ‖Z * Dᴴ‖ + ‖D * Dᴴ‖ := norm_add₃_le
    _ ≤ Real.sqrt 6 * ‖D‖ + Real.sqrt 6 * ‖D‖ + ‖D‖*‖D‖ := by
      rw [hr, hl]
      gcongr
      simpa only [Matrix.frobenius_norm_conjTranspose] using Matrix.frobenius_norm_mul D Dᴴ
    _ = 2 * Real.sqrt 6 * ‖W-Z‖ + ‖W-Z‖^2 := by dsimp [D]; ring

noncomputable def signMatrix (E : Matrix (Fin 6) (Fin 6) ℝ) (s t : ℝ) :
    Matrix (Fin 6) (Fin 6) ℂ := fun i j => ⟨s, t*E i j⟩

theorem signMatrix_gram_re (E : Matrix (Fin 6) (Fin 6) ℝ) (s t : ℝ)
    (hs : s^2=1/6) (ht : t^2=5/6) (i j : Fin 6) :
    ((signMatrix E s t * (signMatrix E s t)ᴴ) i j).re =
      1+(5/6:ℝ)*∑ k, E i k * E j k := by
  have heq (k : Fin 6) :
      (signMatrix E s t i k * star (signMatrix E s t j k)).re =
        (1/6:ℝ)+(5/6:ℝ)*(E i k*E j k) := by
    change s*s-(t*E i k)*(-(t*E j k)) = _
    calc
      _ = s^2+t^2*(E i k*E j k) := by ring
      _ = _ := by rw [hs, ht]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  simp_rw [heq]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem signMatrix_gram_gap (E : Matrix (Fin 6) (Fin 6) ℝ) (s t : ℝ)
    (hs : s^2=1/6) (ht : t^2=5/6)
    (hE : ∀ i j, E i j=1 ∨ E i j= -1) :
    (40/3:ℝ) ≤ ‖signMatrix E s t * (signMatrix E s t)ᴴ -
      (6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)‖^2 := by
  let A := signMatrix E s t * (signMatrix E s t)ᴴ -
      (6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)
  have hentry (i j : Fin 6) : (if i=j then (0:ℝ) else 4/9) ≤ ‖A i j‖^2 := by
    by_cases hij : i=j
    · simp only [hij, ↓reduceIte]
      exact sq_nonneg _
    · have hp (k : Fin 6) : E i k*E j k=1 ∨ E i k*E j k= -1 := by
        rcases hE i k with h | h <;> rcases hE j k with h' | h' <;> simp [h,h']
      have hg := sign_six_gap _ _ _ _ _ _ (hp 0) (hp 1) (hp 2) (hp 3) (hp 4) (hp 5)
      norm_num only [show (2/3:ℝ)^2=4/9 by norm_num] at hg
      have hr : (A i j).re = 1+(5/6:ℝ)*∑ k, E i k*E j k := by
        dsimp [A]
        simp only [Matrix.sub_apply, Complex.sub_re, Matrix.smul_apply, smul_eq_mul,
          Matrix.one_apply_ne hij, mul_zero, Complex.zero_re, sub_zero]
        exact signMatrix_gram_re E s t hs ht i j
      have hgr : (4/9:ℝ) ≤ (A i j).re^2 := by
        rw [hr]
        simpa [Fin.sum_univ_succ, add_assoc] using hg
      simp only [hij, ↓reduceIte]
      nlinarith only [hgr, Complex.sq_norm_sub_sq_re (A i j), sq_nonneg (A i j).im]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 6))) =>
    Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6))) => hentry i j))
  rw [← frobenius_sq] at hsum
  have hcount (i : Fin 6) : (∑ j : Fin 6, if i=j then (0:ℝ) else 4/9) = 20/9 := by
    have heq (j : Fin 6) : (if i=j then (0:ℝ) else 4/9) =
        4/9 - (if i=j then (4/9:ℝ) else 0) := by split_ifs <;> norm_num
    simp_rw [heq]
    norm_num [Finset.sum_sub_distrib]
  simp_rw [hcount] at hsum
  norm_num at hsum
  exact hsum

theorem pointwise_phase_approximation (x y s t : ℝ)
    (hxy : x^2+y^2=1) (hs : s^2=1/6) (ht : t^2=5/6)
    (hs0 : 0≤s) (ht0 : 0≤t) :
    (x-s)^2+(|y|-t)^2 ≤ (225/64:ℝ)*(x-s)^2 := by
  have hx1 : x ≤ 1 := by nlinarith only [hxy, sq_nonneg y, sq_nonneg (x-1)]
  have hxm : -1 ≤ x := by nlinarith only [hxy, sq_nonneg y, sq_nonneg (x+1)]
  have hs1 : s ≤ 5/12 := by nlinarith only [hs, hs0, sq_nonneg (s-5/12)]
  have hyv : |y|^2=y^2 := sq_abs y
  have hcircle : |y|^2-t^2= -(x^2-s^2) := by nlinarith only [hxy, hs, ht, hyv]
  have hbound : (x+s)^2 ≤ (1+s)^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hx1) (show 0≤1+x+2*s by linarith)]
  have hleft : t^2 ≤ (|y|+t)^2 := by
    nlinarith only [sq_nonneg |y|, mul_nonneg (abs_nonneg y) ht0]
  have hprod : t^2*(|y|-t)^2 ≤ (1+s)^2*(x-s)^2 := by
    calc
      t^2*(|y|-t)^2 ≤ (|y|+t)^2*(|y|-t)^2 :=
        mul_le_mul_of_nonneg_right hleft (sq_nonneg _)
      _ = (|y|^2-t^2)^2 := by ring
      _ = (x+s)^2*(x-s)^2 := by rw [hcircle]; ring
      _ ≤ (1+s)^2*(x-s)^2 := mul_le_mul_of_nonneg_right hbound (sq_nonneg _)
  have hc : t^2+(1+s)^2 ≤ (225/64:ℝ)*t^2 := by nlinarith only [ht, hs, hs1]
  have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg (x-s))
  rw [ht] at hprod hmul
  nlinarith only [hprod, hmul]

noncomputable def imaginarySigns (Z : Matrix (Fin 6) (Fin 6) ℂ) :
    Matrix (Fin 6) (Fin 6) ℝ := fun i j => if 0≤(Z i j).im then 1 else -1

theorem imaginarySigns_values (Z : Matrix (Fin 6) (Fin 6) ℂ) (i j : Fin 6) :
    imaginarySigns Z i j=1 ∨ imaginarySigns Z i j= -1 := by
  simp only [imaginarySigns]
  split_ifs <;> simp

theorem sign_rounding_distance (Z : Matrix (Fin 6) (Fin 6) ℂ)
    (hZ : ∀ i j, ‖Z i j‖=1) (s t : ℝ)
    (hs : s^2=1/6) (ht : t^2=5/6) (hs0 : 0≤s) (ht0 : 0≤t) :
    ‖Z-signMatrix (imaginarySigns Z) s t‖^2 ≤
      (225/64:ℝ)*∑ i, ∑ j, ((Z i j).re-s)^2 := by
  have hentry (i j : Fin 6) :
      ‖(Z-signMatrix (imaginarySigns Z) s t) i j‖^2 ≤
        (225/64:ℝ)*((Z i j).re-s)^2 := by
    have hc : (Z i j).re^2+(Z i j).im^2=1 := by
      have hh := Complex.sq_norm (Z i j)
      rw [hZ i j] at hh
      simpa only [one_pow, Complex.normSq_apply, pow_two, one_mul] using hh.symm
    have hp := pointwise_phase_approximation (Z i j).re (Z i j).im s t hc hs ht hs0 ht0
    have heq : ‖(Z-signMatrix (imaginarySigns Z) s t) i j‖^2 =
        ((Z i j).re-s)^2+(|(Z i j).im|-t)^2 := by
      rw [Complex.sq_norm]
      simp only [Complex.normSq_apply, Matrix.sub_apply, Complex.sub_re, Complex.sub_im,
        signMatrix, imaginarySigns]
      split_ifs with hi
      · rw [abs_of_nonneg hi]
        ring
      · rw [abs_of_neg (lt_of_not_ge hi)]
        ring
    rw [heq]
    exact hp
  rw [frobenius_sq]
  calc
    _ ≤ ∑ i, ∑ j, (225/64:ℝ)*((Z i j).re-s)^2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hentry i j
    _ = _ := by simp_rw [Finset.mul_sum]

/-- Every complex Hadamard matrix of order six has a uniform positive real-phase defect. -/
theorem hadamard_phase_gap (Z : Matrix (Fin 6) (Fin 6) ℂ)
    (hflat : ∀ i j, ‖Z i j‖=1)
    (horth : Z*Zᴴ=(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)) :
    (1/9:ℝ) ≤ ∑ i, ∑ j, ((Z i j).re-1/Real.sqrt 6)^2 := by
  let s : ℝ := 1/Real.sqrt 6
  let t : ℝ := Real.sqrt (5/6)
  have hs : s^2=1/6 := by norm_num [s, div_pow, Real.sq_sqrt]
  have ht : t^2=5/6 := by dsimp [t]; rw [Real.sq_sqrt] <;> norm_num
  have hs0 : 0≤s := by dsimp [s]; positivity
  have ht0 : 0≤t := by dsimp [t]; positivity
  let W := signMatrix (imaginarySigns Z) s t
  have hlow : (40/3:ℝ) ≤ ‖W*Wᴴ-(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)‖^2 :=
    signMatrix_gram_gap _ s t hs ht (imaginarySigns_values Z)
  have hclose := sign_rounding_distance Z hflat s t hs ht hs0 ht0
  by_contra hnot
  have hdelta : (∑ i, ∑ j, ((Z i j).re-s)^2)<(1/9:ℝ) := lt_of_not_ge hnot
  have he2 : ‖Z-W‖^2<(25/64:ℝ) := by
    calc
      _ ≤ (225/64:ℝ)*∑ i, ∑ j, ((Z i j).re-s)^2 := hclose
      _ < (225/64:ℝ)*(1/9) := mul_lt_mul_of_pos_left hdelta (by norm_num)
      _ = 25/64 := by norm_num
  have he : ‖Z-W‖<(5/8:ℝ) := by nlinarith only [he2, norm_nonneg (Z-W)]
  have hsqrt : Real.sqrt (6:ℝ)<5/2 := by
    nlinarith only [Real.sq_sqrt (show (0:ℝ)≤6 by norm_num), Real.sqrt_nonneg (6:ℝ)]
  have hgram : ‖W*Wᴴ-(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)‖ ≤
      2*Real.sqrt 6*‖Z-W‖+‖Z-W‖^2 := by
    simpa only [horth, norm_sub_rev] using gram_perturbation Z W horth
  have hcross : 2*Real.sqrt 6*‖Z-W‖<(25/8:ℝ) := by
    calc
      _ ≤ 5*‖Z-W‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      _ < 5*(5/8:ℝ) := mul_lt_mul_of_pos_left he (by norm_num)
      _ = 25/8 := by norm_num
  have hu : ‖W*Wᴴ-(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)‖<(225/64:ℝ) := by
    nlinarith only [hgram, hcross, he2]
  have hpos : (0:ℝ)<225/64+‖W*Wᴴ-(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)‖ := by positivity
  have hh := mul_pos (sub_pos.mpr hu) hpos
  nlinarith only [hlow, hh]

theorem diagonal_phase_unitary (v : Fin 6 → ℂ) (hv : ∀ i, ‖v i‖=1) :
    Matrix.diagonal v * (Matrix.diagonal v)ᴴ = (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i=j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    change v i * conj (v i) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv i]
    norm_num
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]

theorem hadamard_diagonal_gauge (U : Matrix (Fin 6) (Fin 6) ℂ)
    (hflat : ∀ i j, ‖U i j‖=1)
    (horth : U*Uᴴ=(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ))
    (r c : Fin 6 → ℂ) (hr : ∀ i, ‖r i‖=1) (hc : ∀ i, ‖c i‖=1) :
    let Z := Matrix.diagonal r * U * Matrix.diagonal c
    (∀ i j, ‖Z i j‖=1) ∧ Z*Zᴴ=(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  dsimp only
  constructor
  · intro i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, hr i, hc j, hflat i j, one_mul]
  · rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc
      _ = Matrix.diagonal r * (U * (Matrix.diagonal c * (Matrix.diagonal c)ᴴ) * Uᴴ) *
          (Matrix.diagonal r)ᴴ := by noncomm_ring
      _ = _ := by
        rw [diagonal_phase_unitary c hc, Matrix.mul_one, horth,
          Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_phase_unitary r hr]

theorem bargmann_phase_gap (U V W : Matrix (Fin 6) (Fin 6) ℂ)
    (hU : ∀ i j, ‖U i j‖=1) (hV : ∀ i j, ‖V i j‖=1) (hW : ∀ i j, ‖W i j‖=1)
    (horth : U*Uᴴ=(6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)) :
    (1/27:ℝ) ≤ (1/18:ℝ)*∑ c, ∑ a, ∑ b,
      ((U a b * V b c * W c a).re-1/Real.sqrt 6)^2 := by
  have hc (c : Fin 6) : (1/9:ℝ) ≤ ∑ a, ∑ b,
      ((U a b * V b c * W c a).re-1/Real.sqrt 6)^2 := by
    let Z := Matrix.diagonal (fun a => W c a) * U * Matrix.diagonal (fun b => V b c)
    have hg := hadamard_diagonal_gauge U hU horth (fun a => W c a) (fun b => V b c)
      (hW c) (fun b => hV b c)
    have hp := hadamard_phase_gap Z hg.1 hg.2
    have heq (a b : Fin 6) : Z a b=U a b*V b c*W c a := by
      dsimp [Z]
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      ring
    simpa only [heq] using hp
  have hsum := Finset.sum_le_sum (fun c (_ : c∈(Finset.univ : Finset (Fin 6))) => hc c)
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith only [hsum]

section Bases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def scaledTransition (P Q : OrthonormalBasis (Fin 6) ℂ E) :
    Matrix (Fin 6) (Fin 6) ℂ := (Real.sqrt 6 : ℂ) • P.toBasis.toMatrix Q

theorem scaledTransition_apply (P Q : OrthonormalBasis (Fin 6) ℂ E) (i j : Fin 6) :
    scaledTransition P Q i j = (Real.sqrt 6 : ℂ)*inner ℂ (P i) (Q j) := by
  simp [scaledTransition, Module.Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply]

theorem scaledTransition_orthogonal (P Q : OrthonormalBasis (Fin 6) ℂ E) :
    scaledTransition P Q * (scaledTransition P Q)ᴴ =
      (6:ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  simp only [scaledTransition, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    OrthonormalBasis.toMatrix_orthonormalBasis_self_mul_conjTranspose, smul_smul]
  norm_num [Complex.star_def, ← Complex.ofReal_mul, ← pow_two, Real.sq_sqrt]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem scaledTransition_flat (P Q : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ)) :
    ∀ i j, ‖scaledTransition P Q i j‖=1 := by
  intro i j
  rw [scaledTransition_apply, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg (6:ℝ))]
  apply (sq_eq_sq₀ (by positivity) (by norm_num)).mp
  rw [mul_pow, Real.sq_sqrt (by norm_num), hPQ i j]
  norm_num

/-- A quantitative triple-phase defect for three actual mutually unbiased orthonormal bases. -/
theorem orthonormal_triple_phase_gap (P Q R : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=(1/6:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=(1/6:ℝ)) :
    (1/27:ℝ) ≤ (1/18:ℝ)*∑ c, ∑ a, ∑ b,
      ((scaledTransition P Q a b * scaledTransition Q R b c *
        scaledTransition R P c a).re-1/Real.sqrt 6)^2 :=
  bargmann_phase_gap _ _ _ (scaledTransition_flat P Q hPQ)
    (scaledTransition_flat Q R hQR) (scaledTransition_flat R P hRP)
    (scaledTransition_orthogonal P Q)

noncomputable def basisKetBra (B : OrthonormalBasis (Fin 6) ℂ E) (x y : E) :
    Matrix (Fin 6) (Fin 6) ℂ := Matrix.vecMulVec (B.repr x) (star (B.repr y))

theorem repr_dot_inner (B : OrthonormalBasis (Fin 6) ℂ E) (x y : E) :
    star (B.repr x) ⬝ᵥ B.repr y = inner ℂ x y := by
  simpa only [dotProduct, Pi.star_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply] using
    B.repr.inner_map_map x y

theorem basisKetBra_mul (B : OrthonormalBasis (Fin 6) ℂ E) (x y z w : E) :
    basisKetBra B x y * basisKetBra B z w = inner ℂ y z • basisKetBra B x w := by
  rw [basisKetBra, basisKetBra, Matrix.vecMulVec_mul_vecMulVec, repr_dot_inner]
  ext i j
  simp only [basisKetBra, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem basisKetBra_trace (B : OrthonormalBasis (Fin 6) ℂ E) (x y : E) :
    Matrix.trace (basisKetBra B x y) = inner ℂ y x := by
  rw [basisKetBra, Matrix.trace_vecMulVec, dotProduct_comm]
  exact repr_dot_inner B y x

theorem basis_projector_sandwich (B : OrthonormalBasis (Fin 6) ℂ E) (x y z : E) :
    basisKetBra B x x * basisKetBra B y y * basisKetBra B z z * basisKetBra B x x =
      (inner ℂ x y * inner ℂ y z * inner ℂ z x) • basisKetBra B x x := by
  rw [basisKetBra_mul, Matrix.smul_mul, basisKetBra_mul, smul_smul,
    Matrix.smul_mul, basisKetBra_mul, smul_smul]

noncomputable def rankOneDefect (B : OrthonormalBasis (Fin 6) ℂ E) (x y z : E) :
    Matrix (Fin 6) (Fin 6) ℂ :=
  basisKetBra B x x * (basisKetBra B y y * basisKetBra B z z +
    basisKetBra B z z * basisKetBra B y y) * basisKetBra B x x -
    (1/18:ℂ) • basisKetBra B x x

theorem rankOneDefect_formula (B : OrthonormalBasis (Fin 6) ℂ E) (x y z : E) :
    rankOneDefect B x y z =
      ((2*(inner ℂ x y * inner ℂ y z * inner ℂ z x).re-1/18:ℝ):ℂ) • basisKetBra B x x := by
  have hc : inner ℂ x z * inner ℂ z y * inner ℂ y x =
      conj (inner ℂ x y * inner ℂ y z * inner ℂ z x) := by
    simp only [map_mul, inner_conj_symm]
    ring
  unfold rankOneDefect
  rw [Matrix.mul_add, Matrix.add_mul]
  simp only [← Matrix.mul_assoc, basis_projector_sandwich]
  rw [← add_smul, ← sub_smul, hc, Complex.add_conj]
  congr 1
  push_cast
  ring

theorem rankOneDefect_trace_square (B : OrthonormalBasis (Fin 6) ℂ E) (x y z : E)
    (hx : ‖x‖=1) :
    (Matrix.trace ((rankOneDefect B x y z)^2)).re =
      (2*(inner ℂ x y * inner ℂ y z * inner ℂ z x).re-1/18)^2 := by
  have hxx : inner ℂ x x=1 := by
    rw [inner_self_eq_norm_sq_to_K, hx]
    norm_num
  rw [rankOneDefect_formula, pow_two, Matrix.smul_mul, Matrix.mul_smul,
    basisKetBra_mul, hxx, one_smul, smul_smul, Matrix.trace_smul,
    basisKetBra_trace, hxx]
  simp
  ring

theorem scaled_bargmann_re (a b c : ℂ) :
    (((Real.sqrt 6:ℂ)*a)*((Real.sqrt 6:ℂ)*b)*((Real.sqrt 6:ℂ)*c)).re =
      6*Real.sqrt 6*(a*b*c).re := by
  have hs : (Real.sqrt 6:ℂ)^2=6 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have heq : ((Real.sqrt 6:ℂ)*a)*((Real.sqrt 6:ℂ)*b)*((Real.sqrt 6:ℂ)*c) =
      (Real.sqrt 6:ℂ)^2*(Real.sqrt 6:ℂ)*(a*b*c) := by ring
  rw [heq, hs]
  simp

theorem phase_coefficient_square (r : ℝ) :
    (6*Real.sqrt 6*r-1/Real.sqrt 6)^2=54*(2*r-1/18)^2 := by
  have hs : (Real.sqrt (6:ℝ))^2=6 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (6:ℝ) ≠ 0 := by positivity
  have hi : 1/Real.sqrt (6:ℝ)=Real.sqrt 6/6 := by
    apply (div_eq_iff hn).2
    nlinarith only [hs]
  rw [hi]
  calc
    _ = (3*Real.sqrt 6*(2*r-1/18))^2 := by congr 1; ring
    _ = _ := by rw [mul_pow, mul_pow, hs]; ring

/-- The rank-one matrix defect has an unconditional trace gap for any MUB triple. -/
theorem orthonormal_triple_trace_gap (B P Q R : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=(1/6:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=(1/6:ℝ)) :
    (1/81:ℝ) ≤ (Matrix.trace (∑ a, ∑ b, ∑ c,
      (rankOneDefect B (P a) (Q b) (R c))^2)).re := by
  have hp := orthonormal_triple_phase_gap P Q R hPQ hQR hRP
  simp_rw [scaledTransition_apply, scaled_bargmann_re, phase_coefficient_square] at hp
  simp_rw [← Finset.mul_sum] at hp
  have heq : (Matrix.trace (∑ a, ∑ b, ∑ c,
      (rankOneDefect B (P a) (Q b) (R c))^2)).re =
      ∑ c, ∑ a, ∑ b, (2*(inner ℂ (P a) (Q b)*inner ℂ (Q b) (R c)*inner ℂ (R c) (P a)).re-1/18)^2 := by
    simp only [Matrix.trace_sum, Complex.re_sum]
    simp_rw [rankOneDefect_trace_square B _ _ _ (P.norm_eq_one _)]
    conv_lhs =>
      arg 2
      ext a
      rw [Finset.sum_comm]
    exact Finset.sum_comm
  rw [heq]
  nlinarith only [hp]

theorem basisKetBra_self_isStarProjection (B : OrthonormalBasis (Fin 6) ℂ E) (x : E)
    (hx : ‖x‖=1) : IsStarProjection (basisKetBra B x x) := by
  rw [isStarProjection_iff']
  constructor
  · rw [basisKetBra_mul, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  · change (basisKetBra B x x)ᴴ=basisKetBra B x x
    simp [basisKetBra]

theorem basisKetBra_orthogonal (B P : OrthonormalBasis (Fin 6) ℂ E)
    (a b : Fin 6) (hab : a≠b) :
    basisKetBra B (P a) (P a) * basisKetBra B (P b) (P b)=0 := by
  rw [basisKetBra_mul, orthonormal_iff_ite.mp P.orthonormal a b]
  simp [hab]

theorem basisKetBra_complete (B P : OrthonormalBasis (Fin 6) ℂ E) :
    (∑ a, basisKetBra B (P a) (P a))=(1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  calc
    _ = B.toBasis.toMatrix P * (B.toBasis.toMatrix P)ᴴ := by
      ext i j
      simp [basisKetBra, Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Module.Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply]
    _ = 1 := B.toMatrix_orthonormalBasis_self_mul_conjTranspose P

theorem basisKetBra_unbiased (B P Q : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ a b, ‖inner ℂ (P a) (Q b)‖^2=(1/6:ℝ)) (a b : Fin 6) :
    basisKetBra B (P a) (P a) * basisKetBra B (Q b) (Q b) * basisKetBra B (P a) (P a) =
      (1/6:ℝ) • basisKetBra B (P a) (P a) := by
  rw [basisKetBra_mul, Matrix.smul_mul, basisKetBra_mul, smul_smul]
  have hh : inner ℂ (P a) (Q b) * inner ℂ (Q b) (P a)=(1/6:ℂ) := by
    rw [← inner_conj_symm (Q b) (P a), Complex.mul_conj, Complex.normSq_eq_norm_sq, hPQ a b]
    norm_num
  rw [hh]
  ext i j
  simp [Complex.real_smul]

end Bases

end
end SixPhaseGap

namespace MUMSpectral

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

noncomputable def basisPVM (B P : OrthonormalBasis (Fin 6) ℂ E) : PVM 6 6 where
  proj a := SixPhaseGap.basisKetBra B (P a) (P a)
  isProj a := SixPhaseGap.basisKetBra_self_isStarProjection B (P a) (P.norm_eq_one a)
  orthogonal a b hab := SixPhaseGap.basisKetBra_orthogonal B P a b hab
  complete := SixPhaseGap.basisKetBra_complete B P

theorem basisPVM_unbiased (B P Q : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ a b, ‖inner ℂ (P a) (Q b)‖^2=(1/6:ℝ)) :
    Unbiased (basisPVM B P) (basisPVM B Q) := by
  constructor
  · intro a b
    simpa [basisPVM, one_div] using SixPhaseGap.basisKetBra_unbiased B P Q hPQ a b
  · intro a b
    have hQP : ∀ b a, ‖inner ℂ (Q b) (P a)‖^2=(1/6:ℝ) := by
      intro b a
      rw [norm_inner_symm]
      exact hPQ a b
    simpa [basisPVM, one_div] using SixPhaseGap.basisKetBra_unbiased B Q P hQP b a

theorem basisPVM_defect (B P Q R : OrthonormalBasis (Fin 6) ℂ E) (a b c : Fin 6) :
    defect (basisPVM B P) (basisPVM B Q) (basisPVM B R) a b c =
      SixPhaseGap.rankOneDefect B (P a) (Q b) (R c) := by
  unfold defect SixPhaseGap.rankOneDefect
  dsimp only [basisPVM]
  congr 1
  ext i j
  norm_num [Complex.real_smul]

/-- The exact matrix defect interface used by the four-setting harmonic proof. -/
theorem basis_defect_trace_gap (B P Q R : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=(1/6:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=(1/6:ℝ)) :
    (1/81:ℝ) ≤ matTrace (defectSquares (basisPVM B P) (basisPVM B Q) (basisPVM B R)) := by
  unfold matTrace defectSquares
  simp_rw [basisPVM_defect]
  exact SixPhaseGap.orthonormal_triple_trace_gap B P Q R hPQ hQR hRP

end MUMSpectral


namespace MUMNormBounds
set_option maxHeartbeats 300000
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem cross_bound (P Q : M) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (s : ℝ) (hs : 0 < s) (hPQ : P*Q*P = s^2 • P) :
    P*Q+Q*P ≤ s • (P+Q) := by
  have heq : (P*Q-s • Q)*star (P*Q-s • Q) = s • (s • (P+Q)-(P*Q+Q*P)) := by
    simp only [star_sub, star_mul, star_smul, star_trivial,
      hP.isSelfAdjoint.star_eq, hQ.isSelfAdjoint.star_eq,
      mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm]
    rw [show P*Q*(Q*P) = s^2 • P by rw [mul_assoc P Q (Q*P), ← mul_assoc Q Q P, ← mul_assoc,
      hQ.isIdempotentElem.eq, hPQ]]
    rw [show P*Q*Q = P*Q by rw [mul_assoc, hQ.isIdempotentElem.eq]]
    rw [show Q*(Q*P) = Q*P by rw [← mul_assoc, hQ.isIdempotentElem.eq]]
    rw [hQ.isIdempotentElem.eq]
    module
  have hn := star_mul_self_nonneg (star (P*Q-s • Q))
  simp only [star_star] at hn
  rw [heq] at hn
  exact sub_nonneg.mp ((smul_nonneg_iff_nonneg_of_pos_left hs).mp hn)

theorem triple_square_bound (P Q R : M)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (s : ℝ) (hs : 0 < s)
    (hPQ : P*Q*P = s^2 • P) (hPR : P*R*P = s^2 • P) (hQR : Q*R*Q = s^2 • Q) :
    (P+Q+R)^2 ≤ (1+2*s) • (P+Q+R) := by
  have hpq := cross_bound P Q hP hQ s hs hPQ
  have hpr := cross_bound P R hP hR s hs hPR
  have hqr := cross_bound Q R hQ hR s hs hQR
  have h := add_le_add (add_le_add hpq hpr) hqr
  have hleft : (P+Q+R)^2 = P+Q+R + ((P*Q+Q*P)+(P*R+R*P)+(Q*R+R*Q)) := by
    simp only [pow_two, add_mul, mul_add, hP.isIdempotentElem.eq,
      hQ.isIdempotentElem.eq, hR.isIdempotentElem.eq]
    ac_rfl
  rw [hleft]
  calc
    _ ≤ P+Q+R + ((s • (P+Q)+s • (P+R))+s • (Q+R)) := add_le_add le_rfl h
    _ = (1+2*s) • (P+Q+R) := by
      simp only [add_smul, mul_smul, smul_add, one_smul, two_smul]
      ac_rfl

theorem norm_bound_of_square_bound (S : M) (hS : 0 ≤ S) (a : ℝ) (ha : 0 ≤ a)
    (hsq : S^2 ≤ a • S) : ‖S‖ ≤ a := by
  have hself : IsSelfAdjoint S := .of_nonneg hS
  have hn := CStarAlgebra.norm_le_norm_of_nonneg_of_le hself.sq_nonneg hsq
  have hnorm : ‖S^2‖ = ‖S‖^2 := by
    calc
      _ = ‖star S * S‖ := by rw [hself.star_eq, pow_two]
      _ = ‖S‖^2 := by rw [CStarRing.norm_star_mul_self, pow_two]
  rw [hnorm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha] at hn
  nlinarith [norm_nonneg S]

theorem triple_norm_bound (P Q R : M)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (s : ℝ) (hs : 0 < s)
    (hPQ : P*Q*P = s^2 • P) (hPR : P*R*P = s^2 • P) (hQR : Q*R*Q = s^2 • Q) :
    ‖P+Q+R‖ ≤ 1+2*s :=
  norm_bound_of_square_bound _ (add_nonneg (add_nonneg hP.nonneg hQ.nonneg) hR.nonneg)
    _ (by positivity) (triple_square_bound P Q R hP hQ hR s hs hPQ hPR hQR)

theorem triple_order_bound (P Q R : M)
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) (hR : IsStarProjection R)
    (s : ℝ) (hs : 0 < s)
    (hPQ : P*Q*P = s^2 • P) (hPR : P*R*P = s^2 • P) (hQR : Q*R*Q = s^2 • Q) :
    P+Q+R ≤ (1+2*s) • (1:M) := by
  have h := (CStarAlgebra.norm_le_iff_le_algebraMap (P+Q+R) (by positivity : 0 ≤ 1+2*s)
    (add_nonneg (add_nonneg hP.nonneg hQ.nonneg) hR.nonneg)).mp
      (triple_norm_bound P Q R hP hQ hR s hs hPQ hPR hQR)
  simpa only [Algebra.algebraMap_eq_smul_one] using h
end MUMNormBounds


namespace SixSpectralConstants
noncomputable def cubic (t : ℝ) : ℝ := t^3-3*t^2+(5/2)*t-5/9
noncomputable def quartic (t : ℝ) : ℝ := t^4-4*t^3+5*t^2-(20/9)*t+5/18

theorem quartic_positive (t : ℝ) (ht : 21/10 ≤ t) : 0 < quartic t := by
  have he : quartic t = (t-21/10)^4 + (22/5)*(t-21/10)^3 +
      (313/50)*(t-21/10)^2 + (6529/2250)*(t-21/10) + 5869/90000 := by
    unfold quartic
    ring
  have hd : 0 ≤ t-21/10 := sub_nonneg.mpr ht
  rw [he]
  positivity

theorem root_interval (l : ℝ) (hl : IsGreatest {t : ℝ | quartic t=0} l) :
    2 < l ∧ l < 21/10 := by
  have hn : quartic 2 < 0 := by norm_num [quartic]
  have hp := quartic_positive (21/10) le_rfl
  have hc : ContinuousOn quartic (Set.Icc 2 (21/10)) := by unfold quartic; fun_prop
  obtain ⟨t, ht, hz⟩ := intermediate_value_Icc (show (2:ℝ) ≤ 21/10 by norm_num) hc
    (show (0:ℝ) ∈ Set.Icc (quartic 2) (quartic (21/10)) from ⟨hn.le,hp.le⟩)
  have hlt : 2 < t := by
    by_contra hh
    have he : t=2 := le_antisymm (le_of_not_gt hh) ht.1
    rw [he] at hz
    linarith
  constructor
  · exact hlt.trans_le (hl.2 hz)
  · by_contra hh
    have hpos := quartic_positive l (le_of_not_gt hh)
    have hz := hl.1
    change quartic l=0 at hz
    linarith

theorem cubic_interval (l : ℝ) (hl : 2 < l) (hu : l < 21/10) :
    4/9 < cubic l ∧ cubic l < 3/4 := by
  have hd : 0 < l-2 := by linarith
  have hdu : l-2 < 1/10 := by linarith
  have hd2 : (l-2)^2 < 1/100 := by nlinarith
  have hd3 : (l-2)^3 < 1/1000 := by
    have h := mul_lt_mul_of_pos_left hd2 hd
    nlinarith
  have he : cubic l = (l-2)^3+3*(l-2)^2+(5/2)*(l-2)+4/9 := by unfold cubic; ring
  rw [he]
  constructor
  · have hp : 0 < (l-2)^3 := pow_pos hd 3
    nlinarith [sq_nonneg (l-2)]
  · nlinarith

theorem kappa_interval (l : ℝ) (hl : 2 < l) (hu : l < 21/10) :
    1/432 < 1/(216*l*(cubic l)^2) ∧ 1/(216*l*(cubic l)^2) < 3/256 := by
  obtain ⟨hcl,hcu⟩ := cubic_interval l hl hu
  have hc : 0 < cubic l := by linarith
  have hsqlo : (4/9:ℝ)^2 < (cubic l)^2 := by nlinarith
  have hsqup : (cubic l)^2 < (3/4:ℝ)^2 := by nlinarith
  have hden : 0 < 216*l*(cubic l)^2 := by positivity
  have hlo := mul_lt_mul_of_pos_left hsqlo (show 0 < l by linarith)
  have hup := mul_lt_mul_of_pos_left hsqup (show 0 < l by linarith)
  constructor
  · apply (lt_div_iff₀ hden).2
    nlinarith
  · apply (div_lt_iff₀ hden).2
    nlinarith

theorem alpha_stronger (k : ℝ) (hk : 1/432 < k) (hku : k < 3/256) :
    1/540 < k*(1-12*k/(1-6*k)) := by
  have hd : 0 < 1-6*k := by linarith
  have hratio : 12*k/(1-6*k) < 1/5 := by
    apply (div_lt_iff₀ hd).2
    linarith
  have hm := mul_lt_mul_of_pos_left hratio (show 0 < k by linarith)
  nlinarith

theorem alpha_lower (k : ℝ) (hk : 1/432 < k) (hku : k < 3/256) :
    1/600 < k*(1-12*k/(1-6*k)) := by
  have hd : 0 < 1-6*k := by linarith
  have hratio : 12*k/(1-6*k) < 1/5 := by
    apply (div_lt_iff₀ hd).2
    linarith
  have hm := mul_lt_mul_of_pos_left hratio (show 0 < k by linarith)
  nlinarith

theorem resolvent_gap (l : ℝ) (hl : 2 < l) :
    1/6 < l-(1+2/Real.sqrt 6) := by
  have hs : 0 < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (show (0:ℝ) ≤ 6 by norm_num)
  have hb : 12/5 < Real.sqrt 6 := by nlinarith
  have hf : 2/Real.sqrt 6 < 5/6 := (div_lt_iff₀ hs).2 (by linarith)
  linarith
end SixSpectralConstants

open scoped BigOperators
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


namespace MUMSpectral

/-- The rational margin used after the actual operator trace estimate. -/
theorem shifted_trace_lt_six (alpha tau h : ℝ)
    (ha : 1/540 < alpha) (ht : 1/27 ≤ tau)
    (hh : h ≤ (1+6/550000)*(6-alpha*tau)) : h < 6 := by
  have ha0 : 0 < alpha := by linarith
  have hat : (1/14580:ℝ) < alpha*tau := by
    calc
      (1/14580:ℝ) = (1/540)*(1/27) := by norm_num
      _ < alpha*(1/27) := mul_lt_mul_of_pos_right ha (by norm_num)
      _ ≤ alpha*tau := mul_le_mul_of_nonneg_left ht ha0.le
  nlinarith only [hh, hat]

theorem strict_gap_of_shifted_bound (l x : ℝ)
    (h : l+1/550000 ≤ x) : l+1/583200 < x := by linarith

end MUMSpectral

namespace MUMSpectral
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem basis_cycleDefect_trace_gap
    (B P Q R : OrthonormalBasis (Fin 6) ℂ E)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=(1/6:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=(1/6:ℝ)) :
    (1/27:ℝ) ≤ matTrace
      (cycleDefect (basisPVM B P) (basisPVM B Q) (basisPVM B R)) := by
  rw [trace_cycleDefect_eq_three_defectSquares (by norm_num)
    (basisPVM B P) (basisPVM B Q) (basisPVM B R)
    (basisPVM_unbiased B P Q hPQ) (basisPVM_unbiased B Q R hQR)]
  have h := basis_defect_trace_gap B P Q R hPQ hQR hRP
  linarith
end MUMSpectral

namespace MUMSpectral
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem pvm_six_resolvent_gap {D : ℕ} (P Q R : PVM 6 D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot 6 lam) (a b c : Fin 6) :
    (1/6:ℝ) • (1 : Mat D) ≤ lam • 1-(P.proj a+Q.proj b+R.proj c) := by
  have he : ∀ t, quartic 6 t=SixSpectralConstants.quartic t := by
    intro t
    norm_num [quartic, SixSpectralConstants.quartic]
  have hl : IsGreatest {t : ℝ | SixSpectralConstants.quartic t=0} lam := by
    simpa only [LargestRoot, he] using hlam
  have hl2 := (SixSpectralConstants.root_interval lam hl).1
  have hg := SixSpectralConstants.resolvent_gap lam hl2
  have hsq : (1/Real.sqrt (6:ℝ))^2=(1/6:ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have htr := MUMNormBounds.triple_order_bound (P.proj a) (Q.proj b) (R.proj c)
    (P.isProj a) (Q.isProj b) (R.isProj c) (1/Real.sqrt 6) (by positivity)
    (by rw [hsq]; simpa only [one_div, Nat.cast_ofNat] using hPQ.1 a b)
    (by rw [hsq]; simpa only [one_div, Nat.cast_ofNat] using hRP.2 c a)
    (by rw [hsq]; simpa only [one_div, Nat.cast_ofNat] using hQR.1 b c)
  have hc : 1+2*(1/Real.sqrt (6:ℝ))=1+2/Real.sqrt 6 := by ring
  rw [hc] at htr
  calc
    (1/6:ℝ) • (1 : Mat D) ≤ (lam-(1+2/Real.sqrt 6)) • 1 :=
      smul_le_smul_of_nonneg_right hg.le zero_le_one
    _ = lam • 1-(1+2/Real.sqrt 6) • (1 : Mat D) := sub_smul _ _ _
    _ ≤ _ := sub_le_sub_left htr _

end MUMSpectral

namespace MUMSpectral
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
variable {D : ℕ}
local notation "M" => Matrix (Fin D) (Fin D) ℂ

theorem selected_strict_gap_of_trace_deficit
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → Matrix (Fin 6) (Fin 6) ℂ) (T : PVM 6 6)
    (lam alpha tau : ℝ) (hS : ∀ i, 0 ≤ S i)
    (hgap : ∀ i, (1/6:ℝ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) ≤ lam • 1-S i)
    (ha : 1/540 < alpha) (ht : 1/27 ≤ tau)
    (hupper : matTrace ((matrixAverage fun i => (lam • 1-S i)⁻¹)⁻¹) ≤ 6-alpha*tau) :
    ∃ i j, lam+1/583200 < ‖S i+T.proj j‖ := by
  let A := fun i => lam • (1 : Matrix (Fin 6) (Fin 6) ℂ)-S i
  have hA : ∀ i, (A i).PosDef := fun i => posDef_of_scalar_lower (by norm_num) (hgap i)
  have hB : ∀ i, (A i+(1/550000:ℝ) • 1).PosDef := by
    intro i
    exact (hA i).add_posSemidef ((Matrix.PosDef.one.smul (by norm_num : (0:ℝ)<1/550000)).posSemidef)
  have hc := MUMShifted.shifted_harmonic_comparison A (1/6) (1/550000)
    (by norm_num) (by norm_num) hA hB hgap
  have hh := matrix_trace_mono hc
  change matTrace ((matrixAverage fun i => (A i+(1/550000:ℝ) • 1)⁻¹)⁻¹) ≤
    matTrace ((1+(1/550000:ℝ)/(1/6)) • ((matrixAverage fun i => (A i)⁻¹)⁻¹)) at hh
  have hs : ∀ i, A i+(1/550000:ℝ) • 1=(lam+1/550000) • 1-S i := by
    intro i
    dsimp [A]
    module
  simp_rw [hs] at hh
  simp only [matTrace, Matrix.trace_smul, Complex.smul_re, smul_eq_mul] at hh
  have hu : matTrace ((matrixAverage fun i => ((lam+1/550000) • 1-S i)⁻¹)⁻¹) < 6 := by
    apply shifted_trace_lt_six alpha tau _ ha ht
    calc
      _ ≤ (1+6/550000)*matTrace ((matrixAverage fun i => (A i)⁻¹)⁻¹) := by
        convert hh using 1 <;> norm_num [matTrace]
      _ ≤ (1+6/550000)*(6-alpha*tau) :=
        mul_le_mul_of_nonneg_left hupper (by norm_num)
  obtain ⟨i,j,hij⟩ := selected_norm_of_harmonic_trace (by norm_num) (by norm_num)
    S T (lam+1/550000) hS (fun _ => hu.le)
  exact ⟨i,j, strict_gap_of_shifted_bound lam _ hij⟩

end MUMSpectral

namespace MUMSpectral
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem pvm_six_strict_gap (P Q R T : PVM 6 6)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot 6 lam)
    (ht : (1/27:ℝ) ≤ matTrace (cycleDefect P Q R)) :
    ∃ a b c d : Fin 6, lam+1/583200 < ‖selectedSum P Q R T a b c d‖ := by
  have he : ∀ t, quartic 6 t=SixSpectralConstants.quartic t := by
    intro t
    norm_num [quartic, SixSpectralConstants.quartic]
  have hl : IsGreatest {t : ℝ | SixSpectralConstants.quartic t=0} lam := by
    simpa only [LargestRoot, he] using hlam
  obtain ⟨hl2,hlu⟩ := SixSpectralConstants.root_interval lam hl
  have hk := SixSpectralConstants.kappa_interval lam hl2 hlu
  have hke : cycleKappa 6 lam=1/(216*lam*(SixSpectralConstants.cubic lam)^2) := by
    norm_num [cycleKappa, cubic, SixSpectralConstants.cubic]
  rw [← hke] at hk
  have ha := SixSpectralConstants.alpha_stronger (cycleKappa 6 lam) hk.1 hk.2
  have hgap (abc : Fin 6 × (Fin 6 × Fin 6)) :
      (1/6:ℝ) • (1 : Mat 6) ≤ lam • 1-tripleSum P Q R abc :=
    pvm_six_resolvent_gap P Q R hPQ hQR hRP lam hlam abc.1 abc.2.1 abc.2.2
  have hres (abc : Fin 6 × (Fin 6 × Fin 6)) :
      (lam • (1 : Mat 6)-tripleSum P Q R abc).PosDef :=
    posDef_of_scalar_lower (by norm_num) (hgap abc)
  have hu := harmonic_trace_deficit P Q R (by norm_num) hPQ hQR hRP lam hlam hres
  obtain ⟨⟨a,b,c⟩,d,hd⟩ := selected_strict_gap_of_trace_deficit (tripleSum P Q R) T lam
    (cycleKappa 6 lam*(1-12*cycleKappa 6 lam/(1-6*cycleKappa 6 lam)))
    (matTrace (cycleDefect P Q R)) (tripleSum_nonneg P Q R) hgap ha ht hu
  exact ⟨a,b,c,d,hd⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Three mutually unbiased orthonormal bases in complex dimension six force a
strict quantitative selected-sum bound against every fourth projective measurement. -/
theorem three_mub_six_strict_selected_sum
    (B P Q R : OrthonormalBasis (Fin 6) ℂ E) (T : PVM 6 6)
    (hPQ : ∀ i j, ‖inner ℂ (P i) (Q j)‖^2=(1/6:ℝ))
    (hQR : ∀ i j, ‖inner ℂ (Q i) (R j)‖^2=(1/6:ℝ))
    (hRP : ∀ i j, ‖inner ℂ (R i) (P j)‖^2=(1/6:ℝ))
    (lam : ℝ) (hlam : LargestRoot 6 lam) :
    ∃ a b c d : Fin 6, lam+1/583200 <
      ‖selectedSum (basisPVM B P) (basisPVM B Q) (basisPVM B R) T a b c d‖ :=
  pvm_six_strict_gap (basisPVM B P) (basisPVM B Q) (basisPVM B R) T
    (basisPVM_unbiased B P Q hPQ) (basisPVM_unbiased B Q R hQR)
    (basisPVM_unbiased B R P hRP) lam hlam
    (basis_cycleDefect_trace_gap B P Q R hPQ hQR hRP)

end MUMSpectral



end

section
open scoped BigOperators
noncomputable section

def productBasisInner (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (a b : Fin 4) (i j : Fin 6) : ℂ :=
  ∑ x, ∑ y, star (B a i x y) * B b j x y

def productBasisEnergy (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ) : ℝ :=
  ∑ a, ∑ b, if a < b then
    ∑ i, ∑ j, (Complex.normSq (productBasisInner B a b i j) - 1/6)^2 else 0

namespace ProductGeometry

theorem tensor_inner_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u w : ι → ℂ) (v z : κ → ℂ) :
    (∑ x, ∑ y, star (u x*v y)*(w x*z y)) =
      (∑ x, star (u x)*w x)*(∑ y, star (v y)*z y) := by
  rw [Finset.sum_mul_sum]
  simp only [star_mul]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem tensor_norm_factor {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u : ι → ℂ) (v : κ → ℂ) :
    (∑ x, ∑ y, Complex.normSq (u x*v y)) =
      (∑ x, Complex.normSq (u x))*(∑ y, Complex.normSq (v y)) := by
  simp only [Complex.normSq_mul, Finset.sum_mul_sum]

theorem normalized_tensor_factors {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : ι → κ → ℂ)
    (hunit : ∑ x, ∑ y, Complex.normSq (B x y) = 1)
    (hproduct : ∃ (u : ι → ℂ) (v : κ → ℂ), ∀ x y, B x y=u x*v y) :
    ∃ (u : ι → ℂ) (v : κ → ℂ),
      (∑ x, Complex.normSq (u x))=1 ∧
      (∑ y, Complex.normSq (v y))=1 ∧ ∀ x y, B x y=u x*v y := by
  obtain ⟨u,v,hB⟩ := hproduct
  have hmul : (∑ x, Complex.normSq (u x))*(∑ y, Complex.normSq (v y))=1 := by
    rw [← tensor_norm_factor]
    simpa only [hB] using hunit
  have hs : 0 < ∑ x, Complex.normSq (u x) := by
    have hn : 0 ≤ ∑ x, Complex.normSq (u x) :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hz : (∑ x, Complex.normSq (u x)) ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hmul
      norm_num at hmul
    exact lt_of_le_of_ne hn (Ne.symm hz)
  let r : ℝ := Real.sqrt (∑ x, Complex.normSq (u x))
  have hr : 0 < r := Real.sqrt_pos.2 hs
  have hr2 : r^2=∑ x, Complex.normSq (u x) := Real.sq_sqrt hs.le
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  refine ⟨fun x => u x/(r:ℂ), fun y => (r:ℂ)*v y, ?_, ?_, ?_⟩
  · simp only [Complex.normSq_div, Complex.normSq_ofReal, ← Finset.sum_div]
    rw [← hr2]
    field_simp
  · simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← Finset.mul_sum]
    nlinarith
  · intro x y
    rw [hB]
    field_simp

theorem raw_basis_has_normalized_factors
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j = if i=j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y = u x*v y) :
    ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      (∑ x, Complex.normSq (u x))=1 ∧
      (∑ y, Complex.normSq (v y))=1 ∧ ∀ x y, B a i x y=u x*v y := by
  intro a i
  apply normalized_tensor_factors (B a i) _ (hproduct a i)
  have h := congrArg Complex.re (horth a i i)
  simpa [productBasisInner, Complex.normSq_apply, Complex.mul_re] using h

theorem qubit_lagrange (a b c d : ℂ) :
    Complex.normSq (star a*c+star b*d)+Complex.normSq (a*d-b*c) =
      (Complex.normSq a+Complex.normSq b)*(Complex.normSq c+Complex.normSq d) := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

def bloch (u : Fin 2 → ℂ) : Fin 3 → ℝ :=
  ![2*(star (u 0)*u 1).re, 2*(star (u 0)*u 1).im,
    Complex.normSq (u 0)-Complex.normSq (u 1)]

theorem bloch_norm (u : Fin 2 → ℂ) :
    (∑ k, (bloch u k)^2) = (∑ k, Complex.normSq (u k))^2 := by
  simp [bloch, Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem bloch_overlap (u v : Fin 2 → ℂ) :
    2*Complex.normSq (∑ k, star (u k)*v k) =
      (∑ k, Complex.normSq (u k))*(∑ k, Complex.normSq (v k)) +
        ∑ k, bloch u k*bloch v k := by
  simp [bloch, Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem raw_basis_complete
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j = if i=j then 1 else 0)
    (a : Fin 4) (x x' : Fin 2) (y y' : Fin 3) :
    (∑ i, B a i x y * star (B a i x' y')) =
      if x=x' ∧ y=y' then 1 else 0 := by
  let A : Matrix (Fin 6) (Fin 2 × Fin 3) ℂ :=
    fun i xy => star (B a i xy.1 xy.2)
  have hA : A*A.conjTranspose=1 := by
    ext i j
    change (∑ xy : Fin 2 × Fin 3,
      star (B a i xy.1 xy.2)*star (star (B a j xy.1 xy.2))) =
        if i=j then 1 else 0
    simpa only [star_star, Fintype.sum_prod_type, productBasisInner] using horth a i j
  have hrev : A.conjTranspose*A=1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (Fin 6) (Fin 2 × Fin 3) ℂ (by decide :
      Fintype.card (Fin 6)=Fintype.card (Fin 2 × Fin 3))).mp hA
  have hh := congrArg (fun M : Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ =>
    M (x,y) (x',y')) hrev
  change (∑ i, star (star (B a i x y))*star (B a i x' y')) =
    (if (x,y)=(x',y') then 1 else 0) at hh
  simpa only [star_star, Prod.mk.injEq] using hh

theorem orthogonal_qubits_antipodal (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1)
    (horth : (∑ k, star (u k)*v k)=0) :
    ∀ k, bloch u k = -bloch v k := by
  have hn := bloch_norm u
  have hm := bloch_norm v
  have hip := bloch_overlap u v
  rw [hu] at hn
  rw [hv] at hm
  rw [hu, hv, horth] at hip
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hn hm hip
  simp only [map_zero, mul_zero, one_pow, one_mul] at hn hm hip
  change bloch u 0^2+(bloch u 1^2+bloch u 2^2)=1 at hn
  change bloch v 0^2+(bloch v 1^2+bloch v 2^2)=1 at hm
  change 0=1+(bloch u 0*bloch v 0+(bloch u 1*bloch v 1+bloch u 2*bloch v 2)) at hip
  have hs0 : (bloch u 0+bloch v 0)^2=0 := by
    nlinarith [sq_nonneg (bloch u 1+bloch v 1), sq_nonneg (bloch u 2+bloch v 2)]
  have hs1 : (bloch u 1+bloch v 1)^2=0 := by
    nlinarith [sq_nonneg (bloch u 0+bloch v 0), sq_nonneg (bloch u 2+bloch v 2)]
  have hs2 : (bloch u 2+bloch v 2)^2=0 := by
    nlinarith [sq_nonneg (bloch u 0+bloch v 0), sq_nonneg (bloch u 1+bloch v 1)]
  have he0 := sq_eq_zero_iff.mp hs0
  have he1 := sq_eq_zero_iff.mp hs1
  have he2 := sq_eq_zero_iff.mp hs2
  intro k
  fin_cases k
  · change bloch u 0 = -bloch v 0
    linarith
  · change bloch u 1 = -bloch v 1
    linarith
  · change bloch u 2 = -bloch v 2
    linarith

def qubitAxis (u : Fin 2 → ℂ) : Fin 3 → Fin 3 → ℝ :=
  fun x y => bloch u x*bloch u y

theorem unequal_axes_nonorthogonal (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1)
    (hne : qubitAxis u ≠ qubitAxis v) : (∑ k, star (u k)*v k) ≠ 0 := by
  intro ho
  apply hne
  have hp := orthogonal_qubits_antipodal u v hu hv ho
  funext x y
  simp only [qubitAxis, hp, neg_mul_neg]

theorem distinct_axis_blocks_orthogonal
    (B : Fin 6 → Fin 2 → Fin 3 → ℂ)
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (hunit : ∀ i, (∑ k, Complex.normSq (u i k))=1)
    (hfactor : ∀ i x y, B i x y=u i x*v i y)
    (horth : ∀ i j, (∑ x, ∑ y, star (B i x y)*B j x y)=
      if i=j then 1 else 0)
    (i j : Fin 6) (hne : qubitAxis (u i) ≠ qubitAxis (u j)) :
    (∑ y, star (v i y)*v j y)=0 := by
  have hij : i ≠ j := by intro h; subst j; exact hne rfl
  have hh := horth i j
  simp only [hfactor, if_neg hij] at hh
  rw [tensor_inner_factor] at hh
  exact (mul_eq_zero.mp hh).resolve_left
    (unequal_axes_nonorthogonal (u i) (u j) (hunit i) (hunit j) hne)

theorem normSq_inner_cast (w u : Fin 2 → ℂ) :
    (Complex.normSq (∑ x, star (w x)*u x) : ℂ) =
      (star (w 0)*u 0+star (w 1)*u 1)*(w 0*star (u 0)+w 1*star (u 1)) := by
  apply Complex.ext <;>
    simp [Fin.sum_univ_succ, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;>
    ring

theorem tensor_compression
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (w : Fin 2 → ℂ) (hw : (∑ x, Complex.normSq (w x))=1)
    (hres : ∀ x x' y y',
      (∑ i, (u i x*v i y)*star (u i x'*v i y')) =
        if x=x' ∧ y=y' then 1 else 0)
    (y y' : Fin 3) :
    (∑ i, (Complex.normSq (∑ x, star (w x)*u i x) : ℂ)*
      v i y*star (v i y')) = if y=y' then 1 else 0 := by
  have hc : star (w 0)*w 0+star (w 1)*w 1=1 := by
    have hr := congrArg (fun r : ℝ => (r:ℂ)) hw
    simpa [Fin.sum_univ_succ, Complex.normSq_eq_conj_mul_self] using hr
  have heq :
      (∑ i, (Complex.normSq (∑ x, star (w x)*u i x) : ℂ)*v i y*star (v i y')) =
      (star (w 0)*w 0)*(∑ i, (u i 0*v i y)*star (u i 0*v i y')) +
      (star (w 0)*w 1)*(∑ i, (u i 0*v i y)*star (u i 1*v i y')) +
      (star (w 1)*w 0)*(∑ i, (u i 1*v i y)*star (u i 0*v i y')) +
      (star (w 1)*w 1)*(∑ i, (u i 1*v i y)*star (u i 1*v i y')) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [normSq_inner_cast]
    simp only [star_mul]
    ring
  rw [heq, hres, hres, hres, hres]
  by_cases hy : y=y'
  · simpa [hy] using hc
  · simp [hy]

theorem overlap_one_same_bloch (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1)
    (hover : Complex.normSq (∑ k, star (u k)*v k)=1) :
    ∀ k, bloch u k=bloch v k := by
  have hn := bloch_norm u
  have hm := bloch_norm v
  have hip := bloch_overlap u v
  rw [hu] at hn
  rw [hv] at hm
  rw [hu,hv,hover] at hip
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, one_pow, one_mul, mul_one]
    at hn hm hip
  change bloch u 0^2+(bloch u 1^2+bloch u 2^2)=1 at hn
  change bloch v 0^2+(bloch v 1^2+bloch v 2^2)=1 at hm
  change 2=1+(bloch u 0*bloch v 0+(bloch u 1*bloch v 1+bloch u 2*bloch v 2)) at hip
  have hs0 : (bloch u 0-bloch v 0)^2=0 := by
    nlinarith [sq_nonneg (bloch u 1-bloch v 1), sq_nonneg (bloch u 2-bloch v 2)]
  have hs1 : (bloch u 1-bloch v 1)^2=0 := by
    nlinarith [sq_nonneg (bloch u 0-bloch v 0), sq_nonneg (bloch u 2-bloch v 2)]
  have hs2 : (bloch u 2-bloch v 2)^2=0 := by
    nlinarith [sq_nonneg (bloch u 0-bloch v 0), sq_nonneg (bloch u 1-bloch v 1)]
  have he0 := sq_eq_zero_iff.mp hs0
  have he1 := sq_eq_zero_iff.mp hs1
  have he2 := sq_eq_zero_iff.mp hs2
  intro k
  fin_cases k
  · change bloch u 0=bloch v 0
    linarith
  · change bloch u 1=bloch v 1
    linarith
  · change bloch u 2=bloch v 2
    linarith

theorem same_axis_iff_extreme_overlap (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1) :
    qubitAxis u=qubitAxis v ↔
      Complex.normSq (∑ k, star (u k)*v k)=0 ∨
      Complex.normSq (∑ k, star (u k)*v k)=1 := by
  constructor
  · intro haxis
    have hdot : (∑ k, bloch u k*bloch v k)^2=1 := by
      calc
        _ = ∑ x, ∑ y, qubitAxis u x y*qubitAxis v x y := by
          simp [qubitAxis, Fin.sum_univ_succ]
          ring
        _ = ∑ x, ∑ y, (qubitAxis v x y)^2 := by rw [haxis]; simp [sq]
        _ = (∑ k, (bloch v k)^2)^2 := by
          simp [qubitAxis, Fin.sum_univ_succ]
          ring
        _ = 1 := by rw [bloch_norm, hv]; norm_num
    have ho := bloch_overlap u v
    rw [hu,hv] at ho
    have hvalue : (∑ k, bloch u k*bloch v k) =
        2*Complex.normSq (∑ k, star (u k)*v k)-1 := by linarith
    rw [hvalue] at hdot
    have hm : Complex.normSq (∑ k, star (u k)*v k)*
        (Complex.normSq (∑ k, star (u k)*v k)-1)=0 := by nlinarith
    rcases mul_eq_zero.mp hm with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  · rintro (hz | ho)
    · have hp := orthogonal_qubits_antipodal u v hu hv (Complex.normSq_eq_zero.mp hz)
      funext x y
      simp only [qubitAxis,hp,neg_mul_neg]
    · have hp := overlap_one_same_bloch u v hu hv ho
      funext x y
      simp only [qubitAxis,hp]

def qubitPerp (w : Fin 2 → ℂ) : Fin 2 → ℂ := ![-star (w 1), star (w 0)]

theorem qubitPerp_norm (w : Fin 2 → ℂ) :
    (∑ x, Complex.normSq (qubitPerp w x)) = ∑ x, Complex.normSq (w x) := by
  simp [qubitPerp, Fin.sum_univ_succ, add_comm]

theorem qubitPerp_overlap (w u : Fin 2 → ℂ) :
    Complex.normSq (∑ x, star (w x)*u x) +
      Complex.normSq (∑ x, star (qubitPerp w x)*u x) =
      (∑ x, Complex.normSq (w x))*(∑ x, Complex.normSq (u x)) := by
  simp [qubitPerp, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem tensor_compression_complement
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (w : Fin 2 → ℂ) (hw : (∑ x, Complex.normSq (w x))=1)
    (hu : ∀ i, (∑ x, Complex.normSq (u i x))=1)
    (hres : ∀ x x' y y',
      (∑ i, (u i x*v i y)*star (u i x'*v i y')) =
        if x=x' ∧ y=y' then 1 else 0)
    (y y' : Fin 3) :
    (∑ i, ((1-Complex.normSq (∑ x, star (w x)*u i x):ℝ):ℂ)*
      v i y*star (v i y')) = if y=y' then 1 else 0 := by
  have hp (i : Fin 6) : Complex.normSq (∑ x, star (qubitPerp w x)*u i x)=
      1-Complex.normSq (∑ x, star (w x)*u i x) := by
    have hh := qubitPerp_overlap w (u i)
    rw [hw,hu] at hh
    linarith
  simpa only [hp] using tensor_compression u v (qubitPerp w)
    (by rw [qubitPerp_norm,hw]) hres y y'

def qutritProjector (v : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun y y' => v y*star (v y')

theorem qutritProjector_star (v : Fin 3 → ℂ) :
    star (qutritProjector v)=qutritProjector v := by
  ext y y'
  simp [Matrix.star_apply,qutritProjector,star_mul]

theorem qutritProjector_orthogonal (v z : Fin 3 → ℂ)
    (h : (∑ y, star (v y)*z y)=0) :
    qutritProjector v*qutritProjector z=0 := by
  ext y y'
  change (∑ k, (v y*star (v k))*(z k*star (z y')))=0
  calc
    _ = v y*(∑ k, star (v k)*z k)*star (z y') := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = 0 := by rw [h]; simp

theorem mixed_class_projectors_orthogonal
    (B : Fin 6 → Fin 2 → Fin 3 → ℂ)
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (hunit : ∀ i, (∑ k, Complex.normSq (u i k))=1)
    (hfactor : ∀ i x y, B i x y=u i x*v i y)
    (horth : ∀ i j, (∑ x, ∑ y, star (B i x y)*B j x y)=
      if i=j then 1 else 0)
    (w : Fin 2 → ℂ) (hw : (∑ x, Complex.normSq (w x))=1)
    (i j : Fin 6)
    (hi0 : Complex.normSq (∑ x, star (w x)*u i x) ≠ 0)
    (hi1 : Complex.normSq (∑ x, star (w x)*u i x) ≠ 1)
    (hj : Complex.normSq (∑ x, star (w x)*u j x)=0 ∨
      Complex.normSq (∑ x, star (w x)*u j x)=1) :
    qutritProjector (v i)*qutritProjector (v j)=0 := by
  apply qutritProjector_orthogonal
  apply distinct_axis_blocks_orthogonal B u v hunit hfactor horth i j
  intro heq
  have hjaxis := (same_axis_iff_extreme_overlap w (u j) hw (hunit j)).mpr hj
  have hh := (same_axis_iff_extreme_overlap w (u i) hw (hunit i)).mp
    (hjaxis.trans heq.symm)
  exact hh.elim hi0 hi1

end ProductGeometry


open scoped BigOperators
namespace BalancedProductBlocks
noncomputable section

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def plusBlock (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ) : Matrix κ κ ℂ :=
  ∑ i, if c i=1 then Q i else 0
def minusBlock (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ) : Matrix κ κ ℂ :=
  ∑ i, if c i=0 then Q i else 0

theorem plus_fixes_class (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ)
    (hres : ∑ i, (c i : ℂ) • Q i = 1)
    (horth : ∀ i j, c i ≠ 0 → c i ≠ 1 → (c j=0 ∨ c j=1) → Q i*Q j=0)
    (j : ι) (hj : c j=0 ∨ c j=1) : plusBlock Q c * Q j=Q j := by
  calc
    _ = ∑ i, (if c i=1 then Q i else 0)*Q j := by rw [plusBlock,Finset.sum_mul]
    _ = ∑ i, (c i : ℂ) • (Q i*Q j) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i=1
      · simp [hi]
      · by_cases hz : c i=0
        · simp [hi,hz]
        · simp [hi,horth i j hz hi hj]
    _ = (∑ i, (c i : ℂ) • Q i)*Q j := by simp only [Finset.sum_mul,smul_mul_assoc]
    _ = Q j := by rw [hres,one_mul]

theorem minus_fixes_class (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ)
    (hres : ∑ i, ((1-c i : ℝ) : ℂ) • Q i = 1)
    (horth : ∀ i j, c i ≠ 0 → c i ≠ 1 → (c j=0 ∨ c j=1) → Q i*Q j=0)
    (j : ι) (hj : c j=0 ∨ c j=1) : minusBlock Q c * Q j=Q j := by
  calc
    _ = ∑ i, (if c i=0 then Q i else 0)*Q j := by rw [minusBlock,Finset.sum_mul]
    _ = ∑ i, ((1-c i : ℝ) : ℂ) • (Q i*Q j) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : c i=0
      · simp [hi]
      · by_cases ho : c i=1
        · simp [hi,ho]
        · simp [hi,horth i j hi ho hj]
    _ = (∑ i, ((1-c i : ℝ) : ℂ) • Q i)*Q j := by
      simp only [Finset.sum_mul,smul_mul_assoc]
    _ = Q j := by rw [hres,one_mul]

theorem balanced_blocks (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ)
    (hstar : ∀ i, star (Q i)=Q i)
    (hres : ∑ i, (c i : ℂ) • Q i = 1)
    (hres' : ∑ i, ((1-c i : ℝ) : ℂ) • Q i = 1)
    (horth : ∀ i j, c i ≠ 0 → c i ≠ 1 → (c j=0 ∨ c j=1) → Q i*Q j=0) :
    plusBlock Q c = minusBlock Q c := by
  have hp : plusBlock Q c * minusBlock Q c = minusBlock Q c := by
    unfold minusBlock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : c j=0
    · simp only [if_pos hj]
      exact plus_fixes_class Q c hres horth j (Or.inl hj)
    · simp [hj]
  have hm : minusBlock Q c * plusBlock Q c = plusBlock Q c := by
    unfold plusBlock
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : c j=1
    · simp only [if_pos hj]
      exact minus_fixes_class Q c hres' horth j (Or.inr hj)
    · simp [hj]
  have hsp : star (plusBlock Q c)=plusBlock Q c := by simp [plusBlock,apply_ite,hstar]
  have hsm : star (minusBlock Q c)=minusBlock Q c := by simp [minusBlock,apply_ite,hstar]
  have hh := congrArg star hp
  rw [star_mul,hsp,hsm,hm] at hh
  exact hh

theorem balanced_counts (Q : ι → Matrix κ κ ℂ) (c : ι → ℝ)
    (htrace : ∀ i, Matrix.trace (Q i)=1)
    (h : plusBlock Q c=minusBlock Q c) :
    (∑ i, if c i=1 then (1:ℂ) else 0) = ∑ i, if c i=0 then (1:ℂ) else 0 := by
  have ht := congrArg Matrix.trace h
  simpa [plusBlock,minusBlock,Matrix.trace_sum,apply_ite,htrace] using ht

end
end BalancedProductBlocks

namespace ProductGeometry

theorem physical_balanced_blocks
    (B : Fin 6 → Fin 2 → Fin 3 → ℂ)
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (hu : ∀ i, (∑ k, Complex.normSq (u i k))=1)
    (hfactor : ∀ i x y, B i x y=u i x*v i y)
    (horth : ∀ i j, (∑ x, ∑ y, star (B i x y)*B j x y)=
      if i=j then 1 else 0)
    (hres : ∀ x x' y y',
      (∑ i, B i x y*star (B i x' y')) =
        if x=x' ∧ y=y' then 1 else 0)
    (w : Fin 2 → ℂ) (hw : (∑ x, Complex.normSq (w x))=1) :
    BalancedProductBlocks.plusBlock (fun i => qutritProjector (v i))
      (fun i => Complex.normSq (∑ x, star (w x)*u i x)) =
    BalancedProductBlocks.minusBlock (fun i => qutritProjector (v i))
      (fun i => Complex.normSq (∑ x, star (w x)*u i x)) := by
  have hfres : ∀ x x' y y',
      (∑ i, (u i x*v i y)*star (u i x'*v i y')) =
        if x=x' ∧ y=y' then 1 else 0 := by
    simpa only [hfactor] using hres
  apply BalancedProductBlocks.balanced_blocks
  · exact fun i => qutritProjector_star (v i)
  · ext y y'
    simpa [Matrix.sum_apply, Matrix.smul_apply, qutritProjector,
      Matrix.one_apply, mul_assoc] using tensor_compression u v w hw hfres y y'
  · ext y y'
    simpa [Matrix.sum_apply, Matrix.smul_apply, qutritProjector,
      Matrix.one_apply, mul_assoc] using
      tensor_compression_complement u v w hw hu hfres y y'
  · exact mixed_class_projectors_orthogonal B u v hu hfactor horth w hw

theorem qutritProjector_trace (v : Fin 3 → ℂ)
    (hv : (∑ y, Complex.normSq (v y))=1) :
    Matrix.trace (qutritProjector v)=1 := by
  change (∑ y, v y*star (v y))=1
  have h (z : ℂ) : z*star z=(Complex.normSq z : ℂ) := by
    apply Complex.ext <;> simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring
  simp only [h, ← Complex.ofReal_sum, hv, Complex.ofReal_one]

theorem physical_balanced_counts
    (B : Fin 6 → Fin 2 → Fin 3 → ℂ)
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (hu : ∀ i, (∑ k, Complex.normSq (u i k))=1)
    (hv : ∀ i, (∑ k, Complex.normSq (v i k))=1)
    (hfactor : ∀ i x y, B i x y=u i x*v i y)
    (horth : ∀ i j, (∑ x, ∑ y, star (B i x y)*B j x y)=
      if i=j then 1 else 0)
    (hres : ∀ x x' y y',
      (∑ i, B i x y*star (B i x' y')) =
        if x=x' ∧ y=y' then 1 else 0)
    (w : Fin 2 → ℂ) (hw : (∑ x, Complex.normSq (w x))=1) :
    (∑ i, if Complex.normSq (∑ x, star (w x)*u i x)=1 then (1:ℂ) else 0) =
    ∑ i, if Complex.normSq (∑ x, star (w x)*u i x)=0 then (1:ℂ) else 0 := by
  exact BalancedProductBlocks.balanced_counts _ _
    (fun i => qutritProjector_trace (v i) (hv i))
    (physical_balanced_blocks B u v hu hfactor horth hres w hw)

theorem same_bloch_iff_overlap_one (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1) :
    bloch u=bloch v ↔ Complex.normSq (∑ k, star (u k)*v k)=1 := by
  constructor
  · intro hb
    have hh := bloch_overlap u v
    rw [hu,hv,hb] at hh
    have hn := bloch_norm v
    rw [hv] at hn
    simp only [←sq] at hh
    nlinarith
  · intro hh
    funext k
    exact overlap_one_same_bloch u v hu hv hh k

theorem opposite_bloch_iff_overlap_zero (u v : Fin 2 → ℂ)
    (hu : (∑ k, Complex.normSq (u k))=1)
    (hv : (∑ k, Complex.normSq (v k))=1) :
    bloch u= -bloch v ↔ Complex.normSq (∑ k, star (u k)*v k)=0 := by
  constructor
  · intro hb
    have hh := bloch_overlap u v
    rw [hu,hv,hb] at hh
    have hn := bloch_norm v
    rw [hv] at hn
    simp only [Pi.neg_apply,neg_mul,←sq,Finset.sum_neg_distrib] at hh
    nlinarith
  · intro hh
    funext k
    exact orthogonal_qubits_antipodal u v hu hv (Complex.normSq_eq_zero.mp hh) k

def qutritQuadratic (A : Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 3 → ℂ) : ℂ :=
  ∑ y, ∑ y', star (z y)*A y y'*z y'

theorem qutritQuadratic_projector (v z : Fin 3 → ℂ) :
    qutritQuadratic (qutritProjector v) z =
      (Complex.normSq (∑ y, star (v y)*z y) : ℂ) := by
  apply Complex.ext <;>
    simp [qutritQuadratic,qutritProjector,Fin.sum_univ_succ,
      Complex.normSq_apply,Complex.mul_re,Complex.mul_im] <;> ring

theorem qutritQuadratic_sum {ι : Type*} [Fintype ι]
    (A : ι → Matrix (Fin 3) (Fin 3) ℂ) (z : Fin 3 → ℂ) :
    qutritQuadratic (∑ i, A i) z=∑ i, qutritQuadratic (A i) z := by
  simp only [qutritQuadratic,Matrix.sum_apply,Finset.mul_sum,Finset.sum_mul]
  simp_rw [Finset.sum_comm (f:=fun y' i => star (z _)*A i _ y'*z y')]
  rw [Finset.sum_comm]

theorem balanced_projector_overlap_sums
    (v : Fin 6 → Fin 3 → ℂ) (c : Fin 6 → ℝ)
    (h : BalancedProductBlocks.plusBlock (fun i => qutritProjector (v i)) c=
      BalancedProductBlocks.minusBlock (fun i => qutritProjector (v i)) c)
    (z : Fin 3 → ℂ) :
    (∑ i, if c i=1 then Complex.normSq (∑ y, star (v i y)*z y) else 0) =
    ∑ i, if c i=0 then Complex.normSq (∑ y, star (v i y)*z y) else 0 := by
  have hh := congrArg (fun A => qutritQuadratic A z) h
  unfold BalancedProductBlocks.plusBlock BalancedProductBlocks.minusBlock at hh
  rw [qutritQuadratic_sum,qutritQuadratic_sum] at hh
  have hf (p : Prop) [Decidable p] (v : Fin 3 → ℂ) :
      qutritQuadratic (if p then qutritProjector v else 0) z=
      if p then (Complex.normSq (∑ y, star (v y)*z y) : ℂ) else 0 := by
    split_ifs
    · exact qutritQuadratic_projector v z
    · simp [qutritQuadratic]
  simp_rw [hf] at hh
  have hh' := congrArg Complex.re hh
  simpa only [Complex.re_sum,apply_ite,Complex.ofReal_re,Complex.zero_re] using hh'

theorem qutrit_reduced_resolution
    (u : Fin 6 → Fin 2 → ℂ) (v : Fin 6 → Fin 3 → ℂ)
    (hu : ∀ i, (∑ x, Complex.normSq (u i x))=1)
    (hres : ∀ x x' y y',
      (∑ i, (u i x*v i y)*star (u i x'*v i y')) =
        if x=x' ∧ y=y' then 1 else 0) :
    (∑ i, qutritProjector (v i)) = (2:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hn (i : Fin 6) : (∑ x, u i x*star (u i x))=1 := by
    have hh := congrArg (fun r : ℝ => (r:ℂ)) (hu i)
    simpa [Complex.normSq_eq_conj_mul_self,mul_comm] using hh
  ext y y'
  change (∑ i, v i y*star (v i y'))=2*(if y=y' then 1 else 0)
  calc
    _ = ∑ i, ∑ x, (u i x*v i y)*star (u i x*v i y') := by
      apply Finset.sum_congr rfl
      intro i hi
      calc
        _ = (∑ x, u i x*star (u i x))*(v i y*star (v i y')) := by rw [hn]; simp
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro x hx
          simp only [star_mul]
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [hres]
      simp

theorem qutrit_transition_sum
    (v : Fin 6 → Fin 3 → ℂ)
    (hres : (∑ i, qutritProjector (v i)) =
      (2:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (z : Fin 3 → ℂ) (hz : (∑ y, Complex.normSq (z y))=1) :
    (∑ i, Complex.normSq (∑ y, star (v i y)*z y))=2 := by
  have hh := congrArg (fun A => qutritQuadratic A z) hres
  rw [qutritQuadratic_sum] at hh
  simp_rw [qutritQuadratic_projector] at hh
  have hr : qutritQuadratic ((2:ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) z=2 := by
    have hn := congrArg (fun r : ℝ => (r:ℂ)) hz
    have hn' : (∑ y, star (z y)*z y)=1 := by
      simpa [Complex.normSq_eq_conj_mul_self] using hn
    simp only [qutritQuadratic,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,if_true]
    calc
      (∑ y, star (z y)*2*z y) = 2*(∑ y, star (z y)*z y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = 2 := by rw [hn']; ring
  rw [hr] at hh
  have hh' := congrArg Complex.re hh
  simpa using hh'

end ProductGeometry

open scoped BigOperators
noncomputable section
namespace ProductCoarseGraining
attribute [local instance 100000] Classical.propDecidable

theorem weighted_square_bound {ι : Type*} [Fintype ι]
    (w a : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) :
    (∑ i, w i*a i)^2 ≤ ∑ i, w i*(a i)^2 := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s:=Finset.univ) (r:=fun i => w i*a i)
    (f:=w) (g:=fun i => w i*(a i)^2)
    (fun i _ => hw i) (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
    (fun i _ => by ring_nf; exact le_rfl)
  simpa only [hs,one_mul] using h

theorem doubly_stochastic_square_contraction {ι : Type*} [Fintype ι]
    (P : ι → ι → ℝ) (a : ι → ℝ)
    (hpos : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j=1) (hcol : ∀ j, ∑ i, P i j=1) :
    (∑ i, (∑ j, P i j*a j)^2) ≤ ∑ j, (a j)^2 := by
  calc
    _ ≤ ∑ i, ∑ j, P i j*(a j)^2 := by
      exact Finset.sum_le_sum fun i _ => weighted_square_bound (P i) a (hpos i) (hrow i)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul,hcol,one_mul]

theorem two_sided_square_contraction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → ι → ℝ) (Q : κ → κ → ℝ) (A : ι → κ → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 ≤ Q i j)
    (hPr : ∀ i, ∑ j, P i j=1) (hPc : ∀ j, ∑ i, P i j=1)
    (hQr : ∀ i, ∑ j, Q i j=1) (hQc : ∀ j, ∑ i, Q i j=1) :
    (∑ i, ∑ j, (∑ k, ∑ l, P i k*Q j l*A k l)^2) ≤
      ∑ i, ∑ j, (A i j)^2 := by
  have hex (i : ι) (j : κ) :
      (∑ k, ∑ l, P i k*Q j l*A k l) =
      ∑ k, P i k*(∑ l, Q j l*A k l) := by
    simp only [Finset.mul_sum,mul_assoc]
  simp_rw [hex]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j, ∑ k, (∑ l, Q j l*A k l)^2 := by
      exact Finset.sum_le_sum fun j _ =>
        doubly_stochastic_square_contraction P (fun k => ∑ l, Q j l*A k l) hP hPr hPc
    _ = ∑ k, ∑ j, (∑ l, Q j l*A k l)^2 := Finset.sum_comm
    _ ≤ _ := by
      exact Finset.sum_le_sum fun k _ =>
        doubly_stochastic_square_contraction Q (A k) hQ hQr hQc

def fiber {ι α : Type*} [Fintype ι] (f : ι → α) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => f j=f i

theorem fiber_nonempty {ι α : Type*} [Fintype ι] (f : ι → α) (i : ι) :
    (fiber f i).Nonempty := by
  exact ⟨i,by simp [fiber]⟩

theorem fiber_eq {ι α : Type*} [Fintype ι] (f : ι → α) (i j : ι)
    (h : f i=f j) : fiber f i=fiber f j := by
  simp only [fiber,h]

def averageMatrix {ι α : Type*} [Fintype ι] (f : ι → α) (i j : ι) : ℝ :=
  if f j=f i then 1/(fiber f i).card else 0

theorem averageMatrix_nonneg {ι α : Type*} [Fintype ι]
    (f : ι → α) (i j : ι) : 0 ≤ averageMatrix f i j := by
  unfold averageMatrix
  split_ifs <;> positivity

theorem averageMatrix_row {ι α : Type*} [Fintype ι]
    (f : ι → α) (i : ι) : (∑ j, averageMatrix f i j)=1 := by
  have hn : ((fiber f i).card : ℝ)≠0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fiber_nonempty f i))
  simp only [averageMatrix,← Finset.sum_filter]
  change (∑ _j ∈ fiber f i, 1/((fiber f i).card : ℝ))=1
  simp [hn]

theorem averageMatrix_symm {ι α : Type*} [Fintype ι]
    (f : ι → α) (i j : ι) : averageMatrix f i j=averageMatrix f j i := by
  by_cases h : f i=f j
  · simp [averageMatrix,h,fiber_eq f i j h]
  · simp [averageMatrix,h,Ne.symm h]

theorem averageMatrix_col {ι α : Type*} [Fintype ι]
    (f : ι → α) (j : ι) : (∑ i, averageMatrix f i j)=1 := by
  simp_rw [averageMatrix_symm f _ j]
  exact averageMatrix_row f j

theorem fiber_average_square_contraction {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → β) (A : ι → κ → ℝ) :
    (∑ i, ∑ j, (∑ k, ∑ l, averageMatrix f i k*averageMatrix g j l*A k l)^2) ≤
      ∑ i, ∑ j, (A i j)^2 := by
  exact two_sided_square_contraction _ _ A
    (averageMatrix_nonneg f) (averageMatrix_nonneg g)
    (averageMatrix_row f) (averageMatrix_col f)
    (averageMatrix_row g) (averageMatrix_col g)

theorem averageMatrix_support {ι α : Type*} [Fintype ι]
    (f : ι → α) (i j : ι) (h : averageMatrix f i j≠0) : f j=f i := by
  by_contra hn
  exact h (by simp [averageMatrix,hn])

theorem fiber_average_extract {ι κ α β : Type*}
    [Fintype ι] [Fintype κ] (f : ι → α) (g : κ → β)
    (C A : ι → κ → ℝ)
    (hC : ∀ i j k l, f k=f i → g l=g j → C k l=C i j)
    (i : ι) (j : κ) :
    (∑ k, ∑ l, averageMatrix f i k*averageMatrix g j l*(C k l*A k l)) =
      C i j*(∑ k, ∑ l, averageMatrix f i k*averageMatrix g j l*A k l) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hp : averageMatrix f i k=0
  · simp [hp]
  by_cases hq : averageMatrix g j l=0
  · simp [hq]
  rw [hC i j k l (averageMatrix_support f i k hp) (averageMatrix_support g j l hq)]
  ring

theorem average_preserves_row_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → ι → ℝ) (Q : κ → κ → ℝ) (A : ι → κ → ℝ) (s : ℝ)
    (hPr : ∀ i, ∑ k, P i k=1) (hQc : ∀ l, ∑ j, Q j l=1)
    (hAr : ∀ k, ∑ l, A k l=s) (i : ι) :
    (∑ j, ∑ k, ∑ l, P i k*Q j l*A k l)=s := by
  rw [Finset.sum_comm]
  have hh (k : ι) : (∑ j, ∑ l, P i k*Q j l*A k l)=P i k*s := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ l, P i k*(∑ j, Q j l)*A k l := by
        simp only [Finset.mul_sum,Finset.sum_mul]
      _ = P i k*s := by simp only [hQc,mul_one,← Finset.mul_sum,hAr]
  simp only [hh,← Finset.sum_mul,hPr,one_mul]

theorem average_preserves_col_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → ι → ℝ) (Q : κ → κ → ℝ) (A : ι → κ → ℝ) (s : ℝ)
    (hPc : ∀ k, ∑ i, P i k=1) (hQr : ∀ j, ∑ l, Q j l=1)
    (hAc : ∀ l, ∑ k, A k l=s) (j : κ) :
    (∑ i, ∑ k, ∑ l, P i k*Q j l*A k l)=s := by
  have hh (i : ι) : (∑ k, ∑ l, P i k*Q j l*A k l)=
      ∑ l, ∑ k, Q j l*P i k*A k l := by
    rw [Finset.sum_comm]
    simp only [mul_comm (P i _) (Q j _)]
  simp_rw [hh]
  exact average_preserves_row_sum Q P (fun l k => A k l) s hQr hPc hAc j

theorem row_stochastic_odd_sum_zero {ι : Type*} [Fintype ι]
    (P : ι → ι → ℝ) (f : ι → ℝ)
    (hrow : ∀ i, ∑ j, P i j=1) (hcol : ∀ j, ∑ i, P i j=1)
    (hodd : ∀ i j, P i j≠0 → f j= -f i) : (∑ i, f i)=0 := by
  have h (i j : ι) : P i j*f j= -(P i j*f i) := by
    by_cases hz : P i j=0
    · simp [hz]
    · rw [hodd i j hz]; ring
  have hs : (∑ i, ∑ j, P i j*f j)=∑ j, f j := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul,hcol,one_mul]
  have hs' : (∑ i, ∑ j, P i j*f j)= -(∑ i, f i) := by
    simp only [h,Finset.sum_neg_distrib,← Finset.sum_mul,hrow,one_mul]
  linarith

def oppositeFiber {ι V : Type*} [Fintype ι] [Neg V]
    (b : ι → V) (i : ι) : Finset ι :=
  Finset.univ.filter fun j => b j= -b i

def oppositeAverage {ι V : Type*} [Fintype ι] [Neg V]
    (b : ι → V) (i j : ι) : ℝ :=
  if b j= -b i then 1/(fiber b i).card else 0

theorem oppositeAverage_row {ι V : Type*} [Fintype ι] [Neg V]
    (b : ι → V) (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (i : ι) : (∑ j, oppositeAverage b i j)=1 := by
  have hn : ((fiber b i).card : ℝ)≠0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr (fiber_nonempty b i))
  simp only [oppositeAverage,← Finset.sum_filter]
  change (∑ _j ∈ oppositeFiber b i, 1/((fiber b i).card : ℝ))=1
  simp [hbal,hn]

theorem opposite_fiber_eq {ι V : Type*} [Fintype ι] [AddGroup V]
    (b : ι → V) (i j : ι) (h : b j= -b i) :
    oppositeFiber b i=fiber b j := by
  simp only [oppositeFiber,fiber,h]

theorem oppositeAverage_symm {ι V : Type*} [Fintype ι] [AddGroup V]
    (b : ι → V) (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (i j : ι) : oppositeAverage b i j=oppositeAverage b j i := by
  by_cases h : b j= -b i
  · have hr : b i= -b j := by rw [h,neg_neg]
    have hc : (fiber b i).card=(fiber b j).card := by
      rw [←hbal i,opposite_fiber_eq b i j h]
    simp only [oppositeAverage,if_pos h,if_pos hr,hc]
  · have hr : b i≠ -b j := by
      intro he
      apply h
      rw [he,neg_neg]
    simp [oppositeAverage,h,hr]

theorem balanced_fibers_odd_sum_zero {ι V : Type*} [Fintype ι] [AddGroup V]
    (b : ι → V) (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (f : ι → ℝ) (hodd : ∀ i j, b j= -b i → f j= -f i) :
    (∑ i, f i)=0 := by
  apply row_stochastic_odd_sum_zero (oppositeAverage b) f (oppositeAverage_row b hbal)
  · intro j
    simp_rw [oppositeAverage_symm b hbal _ j]
    exact oppositeAverage_row b hbal j
  · intro i j hij
    apply hodd i j
    by_contra hn
    exact hij (by simp [oppositeAverage,hn])

theorem fiber_average_as_quotient {ι V : Type*} [Fintype ι]
    (b : ι → V) (A : ι → ℝ) (i : ι) :
    (∑ k, averageMatrix b i k*A k) =
      (∑ k, if b k=b i then A k else 0)/(fiber b i).card := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : b k=b i <;> simp [averageMatrix,h,div_eq_mul_inv,mul_comm]

theorem fiber_average_antipodal {ι V : Type*} [Fintype ι] [AddGroup V]
    (b : ι → V) (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (A : ι → ℝ)
    (hA : ∀ i, (∑ k, if b k=b i then A k else 0)=
      ∑ k, if b k= -b i then A k else 0)
    (i j : ι) (h : b j= -b i) :
    (∑ k, averageMatrix b j k*A k) = ∑ k, averageMatrix b i k*A k := by
  rw [fiber_average_as_quotient,fiber_average_as_quotient]
  have hc : (fiber b j).card=(fiber b i).card := by
    rw [← opposite_fiber_eq b i j h,hbal i]
  rw [hc,hA i]
  simp only [h]

theorem two_sided_average_antipodal {ι κ V : Type*}
    [Fintype ι] [Fintype κ] [AddGroup V]
    (b : ι → V) (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (Q : κ → κ → ℝ) (A : ι → κ → ℝ)
    (hA : ∀ i l, (∑ k, if b k=b i then A k l else 0)=
      ∑ k, if b k= -b i then A k l else 0)
    (i i' : ι) (j : κ) (h : b i'= -b i) :
    (∑ k, ∑ l, averageMatrix b i' k*Q j l*A k l) =
      ∑ k, ∑ l, averageMatrix b i k*Q j l*A k l := by
  have hex (t : ι) : (∑ k, ∑ l, averageMatrix b t k*Q j l*A k l)=
      ∑ l, Q j l*(∑ k, averageMatrix b t k*A k l) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hex,hex]
  apply Finset.sum_congr rfl
  intro l hl
  rw [fiber_average_antipodal b hbal (fun k => A k l) (fun t => hA t l) i i' h]

def averagedMatrix {ι κ α β : Type*} [Fintype ι] [Fintype κ]
    (b : ι → α) (c : κ → β) (M : ι → κ → ℝ) (i : ι) (j : κ) : ℝ :=
  ∑ k, ∑ l, averageMatrix b i k*averageMatrix c j l*M k l

theorem product_average_frame_bound {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (b : ι → δ → ℝ) (c : κ → δ → ℝ) (M : ι → κ → ℝ)
    (hbal : ∀ i, (oppositeFiber b i).card=(fiber b i).card)
    (hM : ∀ i l, (∑ k, if b k=b i then M k l else 0)=
      ∑ k, if b k= -b i then M k l else 0) :
    (1/4:ℝ)*(∑ i, ∑ j, (1+(∑ t, b i t*c j t)^2)*
      (averagedMatrix b c M i j)^2) ≤
      ∑ i, ∑ j, (((1+(∑ t, b i t*c j t))/2)*M i j)^2 := by
  let C : ι → κ → ℝ := fun i j => (1+(∑ t, b i t*c j t))/2
  have hC : ∀ i j k l, b k=b i → c l=c j → C k l=C i j := by
    intro i j k l hb hc
    simp only [C,hb,hc]
  have hcs := fiber_average_square_contraction b c (fun i j => C i j*M i j)
  simp_rw [fiber_average_extract b c C M hC] at hcs
  have heven (i i' : ι) (j : κ) (h : b i'= -b i) :
      averagedMatrix b c M i' j=averagedMatrix b c M i j :=
    two_sided_average_antipodal b hbal (averageMatrix c) M hM i i' j h
  have hodd (j : κ) : (∑ i, (∑ t, b i t*c j t)*(averagedMatrix b c M i j)^2)=0 := by
    apply balanced_fibers_odd_sum_zero b hbal
    intro i i' hi
    rw [heven i i' j hi]
    simp only [hi,Pi.neg_apply,neg_mul,Finset.sum_neg_distrib]
  have hz : (∑ i, ∑ j, (∑ t, b i t*c j t)*(averagedMatrix b c M i j)^2)=0 := by
    rw [Finset.sum_comm]
    simp only [hodd,Finset.sum_const_zero]
  have heq : (∑ i, ∑ j, (C i j*averagedMatrix b c M i j)^2) =
      (1/4:ℝ)*(∑ i, ∑ j, (1+(∑ t, b i t*c j t)^2)*
        (averagedMatrix b c M i j)^2) +
      (1/2:ℝ)*(∑ i, ∑ j, (∑ t, b i t*c j t)*(averagedMatrix b c M i j)^2) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [C]
    ring
  change (∑ i, ∑ j, (C i j*averagedMatrix b c M i j)^2) ≤ _ at hcs
  rw [heq,hz,mul_zero,add_zero] at hcs
  exact hcs

end ProductCoarseGraining

namespace ProductPhysicalTransport
open ProductGeometry ProductCoarseGraining

structure NormalizedProductBasis where
  u : Fin 6 → Fin 2 → ℂ
  v : Fin 6 → Fin 3 → ℂ
  hu : ∀ i, (∑ x, Complex.normSq (u i x))=1
  hv : ∀ i, (∑ y, Complex.normSq (v i y))=1
  horth : ∀ i j, (∑ x, ∑ y, star (u i x*v i y)*(u j x*v j y))=
    if i=j then 1 else 0
  hres : ∀ x x' y y', (∑ i, (u i x*v i y)*star (u i x'*v i y'))=
    if x=x' ∧ y=y' then 1 else 0

attribute [local instance 100000] Classical.propDecidable

def NormalizedProductBasis.b (P : NormalizedProductBasis) (i : Fin 6) : Fin 3 → ℝ :=
  bloch (P.u i)

theorem NormalizedProductBasis.balanced (P : NormalizedProductBasis) (i : Fin 6) :
    (oppositeFiber P.b i).card=(fiber P.b i).card := by
  have hh := physical_balanced_counts (fun i x y => P.u i x*P.v i y)
    P.u P.v P.hu P.hv (fun _ _ _ => rfl) P.horth P.hres (P.u i) (P.hu i)
  have hone (k : Fin 6) : Complex.normSq (∑ x, star (P.u i x)*P.u k x)=1 ↔
      P.b k=P.b i := (same_bloch_iff_overlap_one _ _ (P.hu i) (P.hu k)).symm.trans eq_comm
  have hzero (k : Fin 6) : Complex.normSq (∑ x, star (P.u i x)*P.u k x)=0 ↔
      P.b k= -P.b i := by
    rw [←opposite_bloch_iff_overlap_zero _ _ (P.hu i) (P.hu k)]
    change P.b i= -P.b k ↔ P.b k= -P.b i
    constructor <;> intro h <;> rw [h,neg_neg]
  simp_rw [hone,hzero] at hh
  have hc : ((fiber P.b i).card : ℂ)=((oppositeFiber P.b i).card : ℂ) := by
    simpa only [fiber,oppositeFiber,←Finset.sum_filter,Finset.sum_const,
      nsmul_eq_mul,mul_one] using hh
  exact_mod_cast hc.symm

def qutritTransition (P Q : NormalizedProductBasis) (i j : Fin 6) : ℝ :=
  Complex.normSq (∑ y, star (P.v i y)*Q.v j y)

theorem NormalizedProductBasis.balanced_transition
    (P Q : NormalizedProductBasis) (i l : Fin 6) :
    (∑ k, if P.b k=P.b i then qutritTransition P Q k l else 0)=
      ∑ k, if P.b k= -P.b i then qutritTransition P Q k l else 0 := by
  have hb := physical_balanced_blocks (fun i x y => P.u i x*P.v i y)
    P.u P.v P.hu (fun _ _ _ => rfl) P.horth P.hres (P.u i) (P.hu i)
  have hh := balanced_projector_overlap_sums P.v _ hb (Q.v l)
  have hone (k : Fin 6) : Complex.normSq (∑ x, star (P.u i x)*P.u k x)=1 ↔
      P.b k=P.b i := (same_bloch_iff_overlap_one _ _ (P.hu i) (P.hu k)).symm.trans eq_comm
  have hzero (k : Fin 6) : Complex.normSq (∑ x, star (P.u i x)*P.u k x)=0 ↔
      P.b k= -P.b i := by
    rw [←opposite_bloch_iff_overlap_zero _ _ (P.hu i) (P.hu k)]
    change P.b i= -P.b k ↔ P.b k= -P.b i
    constructor <;> intro h <;> rw [h,neg_neg]
  simpa only [hone,hzero,qutritTransition] using hh

def productTransition (P Q : NormalizedProductBasis) (i j : Fin 6) : ℝ :=
  Complex.normSq (∑ x, ∑ y, star (P.u i x*P.v i y)*(Q.u j x*Q.v j y))

def transportH (P Q : NormalizedProductBasis) (i j : Fin 6) : ℝ :=
  3*averagedMatrix P.b Q.b (qutritTransition P Q) i j

theorem product_transition_bloch (P Q : NormalizedProductBasis) (i j : Fin 6) :
    productTransition P Q i j=
      ((1+(∑ t, P.b i t*Q.b j t))/2)*qutritTransition P Q i j := by
  unfold productTransition
  rw [tensor_inner_factor,map_mul]
  have hh := bloch_overlap (P.u i) (Q.u j)
  rw [P.hu,Q.hu] at hh
  change Complex.normSq (∑ x, star (P.u i x)*Q.u j x)*qutritTransition P Q i j=_
  change 2*Complex.normSq (∑ x, star (P.u i x)*Q.u j x)=1*1+∑ t, P.b i t*Q.b j t at hh
  rw [show Complex.normSq (∑ x, star (P.u i x)*Q.u j x)=
    (1+(∑ t, P.b i t*Q.b j t))/2 by linarith]

theorem actual_product_transport_bound (P Q : NormalizedProductBasis) :
    (1/36:ℝ)*(∑ i, ∑ j, (1+(∑ t, P.b i t*Q.b j t)^2)*(transportH P Q i j)^2) ≤
      ∑ i, ∑ j, (productTransition P Q i j)^2 := by
  have hh := product_average_frame_bound P.b Q.b (qutritTransition P Q)
    P.balanced (P.balanced_transition Q)
  simp_rw [←product_transition_bloch P Q] at hh
  calc
    _ = (1/4:ℝ)*(∑ i, ∑ j, (1+(∑ t, P.b i t*Q.b j t)^2)*
        (averagedMatrix P.b Q.b (qutritTransition P Q) i j)^2) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      unfold transportH
      ring
    _ ≤ _ := hh

theorem qutrit_transition_symm (P Q : NormalizedProductBasis) (i j : Fin 6) :
    qutritTransition P Q i j=qutritTransition Q P j i := by
  have hh : (∑ y, star (P.v i y)*Q.v j y)=star (∑ y, star (Q.v j y)*P.v i y) := by
    simp only [star_sum,star_mul,star_star]
  unfold qutritTransition
  rw [hh]
  exact Complex.normSq_conj _

theorem qutrit_transition_col (P Q : NormalizedProductBasis) (j : Fin 6) :
    (∑ i, qutritTransition P Q i j)=2 :=
  qutrit_transition_sum P.v (qutrit_reduced_resolution P.u P.v P.hu P.hres) (Q.v j) (Q.hv j)

theorem qutrit_transition_row (P Q : NormalizedProductBasis) (i : Fin 6) :
    (∑ j, qutritTransition P Q i j)=2 := by
  simp_rw [qutrit_transition_symm P Q i]
  exact qutrit_transition_col Q P i

theorem transportH_row (P Q : NormalizedProductBasis) (i : Fin 6) :
    (∑ j, transportH P Q i j)=6 := by
  simp only [transportH,← Finset.mul_sum]
  have hh := average_preserves_row_sum (averageMatrix P.b) (averageMatrix Q.b)
    (qutritTransition P Q) 2 (averageMatrix_row P.b) (averageMatrix_col Q.b)
    (qutrit_transition_row P Q) i
  change 3*(∑ j, ∑ k, ∑ l, averageMatrix P.b i k*averageMatrix Q.b j l*
    qutritTransition P Q k l)=6
  rw [hh]
  norm_num

theorem transportH_col (P Q : NormalizedProductBasis) (j : Fin 6) :
    (∑ i, transportH P Q i j)=6 := by
  simp only [transportH,← Finset.mul_sum]
  have hh := average_preserves_col_sum (averageMatrix P.b) (averageMatrix Q.b)
    (qutritTransition P Q) 2 (averageMatrix_col P.b) (averageMatrix_row Q.b)
    (qutrit_transition_col P Q) j
  change 3*(∑ i, ∑ k, ∑ l, averageMatrix P.b i k*averageMatrix Q.b j l*
    qutritTransition P Q k l)=6
  rw [hh]
  norm_num

theorem normalized_bases_from_raw
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j=if i=j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y=u x*v y) :
    ∃ P : Fin 4 → NormalizedProductBasis,
      ∀ a i x y, B a i x y=(P a).u i x*(P a).v i y := by
  have ho : ∀ a i j, productBasisInner B a a i j=
      @ite ℂ (i=j) (instDecidableEqFin 6 i j) 1 0 := by
    intro a i j
    by_cases h : i=j
    · simpa only [if_pos h] using horth a i j
    · simpa only [if_neg h] using horth a i j
  choose u v hu hv hf using raw_basis_has_normalized_factors B ho hproduct
  let P : Fin 4 → NormalizedProductBasis := fun a =>
    { u:=u a, v:=v a, hu:=hu a, hv:=hv a
      horth:=by intro i j; simpa only [←hf,productBasisInner] using ho a i j
      hres:=by intro x x' y y'; simpa only [←hf] using raw_basis_complete B ho a x x' y y' }
  exact ⟨P,hf⟩

end ProductPhysicalTransport
open scoped BigOperators

namespace ProductCovariance

theorem weighted_variance {ι : Type*} [Fintype ι]
    (p A : ι → ℝ) (m : ℝ) (hp : ∑ i, p i=1)
    (hm : ∑ i, p i*A i=m) :
    (∑ i, p i*(A i-m)^2) = (∑ i, p i*(A i)^2)-m^2 := by
  have heq : (∑ i, p i*(A i-m)^2) =
      (∑ i, p i*(A i)^2)-2*m*(∑ i, p i*A i)+m^2*(∑ i, p i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, hp, hm]
  ring

theorem weighted_covariance_cauchy {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (p : ι → ℝ) (q : κ → ℝ) (A : ι → δ → ℝ) (B : κ → δ → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) :
    (∑ i, ∑ j, p i*q j*(∑ k, A i k*B j k)^2) ≤
      (∑ i, p i*(∑ k, (A i k)^2))*(∑ j, q j*(∑ k, (B j k)^2)) := by
  calc
    _ ≤ ∑ i, ∑ j, p i*q j*((∑ k, (A i k)^2)*(∑ k, (B j k)^2)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (B j))
        (mul_nonneg (hp i) (hq j))
    _ = _ := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem vector_weighted_variance {ι δ : Type*} [Fintype ι] [Fintype δ]
    (p : ι → ℝ) (A : ι → δ → ℝ) (m : δ → ℝ)
    (hp : ∑ i, p i=1) (hm : ∀ k, ∑ i, p i*A i k=m k) :
    (∑ i, p i*(∑ k, (A i k-m k)^2)) =
      (∑ i, p i*(∑ k, (A i k)^2))-(∑ k, (m k)^2) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun i k => p i*(A i k)^2)]
  simp_rw [weighted_variance p (fun i => A i _) _ hp (hm _)]
  rw [Finset.sum_sub_distrib]

theorem trace_square_bound (M : Fin 3 → Fin 3 → ℝ) :
    (∑ i, M i i)^2 ≤ 3*(∑ i, ∑ j, (M i j)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : Fin 3 => M i i) (fun _ => (1:ℝ))
  have hd : (∑ i, (M i i)^2) ≤ ∑ i, ∑ j, (M i j)^2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact Finset.single_le_sum (fun j hj => sq_nonneg (M i j)) (Finset.mem_univ i)
  norm_num at hc
  nlinarith

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem four_frame_expansion (F : Fin 4 → Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, (∑ a, F a i j)^2) =
      (∑ a, ∑ i, ∑ j, (F a i j)^2) +
        2*(∑ a, ∑ b, if a<b then ∑ i, ∑ j, F a i j*F b i j else 0) := by
  simp only [Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num only [Fin.lt_def, Fin.val_natCast, Fin.val_zero, Fin.val_one,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceLT, if_true, if_false]
  ring

theorem four_trace_frame_bound (F : Fin 4 → Fin 3 → Fin 3 → ℝ)
    (htrace : ∀ a, ∑ i, F a i i=1) :
    2/3 + (∑ a, (1-(∑ i, ∑ j, (F a i j)^2)))/2 ≤
      ∑ a, ∑ b, if a<b then ∑ i, ∑ j, F a i j*F b i j else 0 := by
  have ht : (∑ i, ∑ a, F a i i)=4 := by
    rw [Finset.sum_comm]
    simp [htrace]
  have hc := trace_square_bound (fun i j => ∑ a, F a i j)
  rw [ht, four_frame_expansion] at hc
  have hu : (∑ a, (1-(∑ i, ∑ j, (F a i j)^2))) =
      4-(∑ a, ∑ i, ∑ j, (F a i j)^2) := by
    simp [Finset.sum_sub_distrib]
  rw [hu]
  nlinarith

theorem scalar_transport_centering {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p A : ι → ℝ) (q B : κ → ℝ) (h : ι → κ → ℝ) (F G : ℝ)
    (hrow : ∀ i, ∑ j, q j*h i j=0)
    (hcol : ∀ j, ∑ i, p i*h i j=0) :
    (∑ i, ∑ j, p i*q j*(A i-F)*(B j-G)*h i j) =
      ∑ i, ∑ j, p i*q j*A i*B j*h i j := by
  have ha : (∑ i, ∑ j, p i*q j*A i*G*h i j)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    calc
      _ = p i*A i*G*(∑ j, q j*h i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hrow]; ring
  have hb : (∑ i, ∑ j, p i*q j*F*B j*h i j)=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    calc
      _ = q j*F*B j*(∑ i, p i*h i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by rw [hcol]; ring
  have hc : (∑ i, ∑ j, p i*q j*F*G*h i j)=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    calc
      _ = p i*F*G*(∑ j, q j*h i j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [hrow]; ring
  have heq : (∑ i, ∑ j, p i*q j*(A i-F)*(B j-G)*h i j) =
      (∑ i, ∑ j, p i*q j*A i*B j*h i j)-
      (∑ i, ∑ j, p i*q j*A i*G*h i j)-
      (∑ i, ∑ j, p i*q j*F*B j*h i j)+
      (∑ i, ∑ j, p i*q j*F*G*h i j) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq,ha,hb,hc]
  ring

theorem vector_transport_centering {ι κ δ : Type*}
    [Fintype ι] [Fintype κ] [Fintype δ]
    (p : ι → ℝ) (q : κ → ℝ) (A : ι → δ → ℝ) (B : κ → δ → ℝ)
    (F G : δ → ℝ) (h : ι → κ → ℝ)
    (hrow : ∀ i, ∑ j, q j*h i j=0)
    (hcol : ∀ j, ∑ i, p i*h i j=0) :
    (∑ i, ∑ j, p i*q j*(∑ k, (A i k-F k)*(B j k-G k))*h i j) =
      ∑ i, ∑ j, p i*q j*(∑ k, A i k*B j k)*h i j := by
  have reorder (X : ι → κ → δ → ℝ) :
      (∑ i, ∑ j, p i*q j*(∑ k, X i j k)*h i j)=
      ∑ k, ∑ i, ∑ j, p i*q j*X i j k*h i j := by
    simp only [Finset.mul_sum,Finset.sum_mul]
    simp_rw [Finset.sum_comm (f:=fun j k => p _*q j*X _ j k*h _ j)]
    rw [Finset.sum_comm]
  rw [reorder,reorder]
  apply Finset.sum_congr rfl
  intro k hk
  simpa only [mul_assoc] using scalar_transport_centering p (fun i => A i k) q
    (fun j => B j k) h (F k) (G k) hrow hcol

theorem outer_norm {δ : Type*} [Fintype δ] (b : δ → ℝ) :
    (∑ k : δ × δ, (b k.1*b k.2)^2)=(∑ t, (b t)^2)^2 := by
  rw [Fintype.sum_prod_type,pow_two,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem outer_inner {δ : Type*} [Fintype δ] (b c : δ → ℝ) :
    (∑ k : δ × δ, (b k.1*b k.2)*(c k.1*c k.2))=(∑ t, b t*c t)^2 := by
  rw [Fintype.sum_prod_type,pow_two,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem mean_inner {ι κ δ : Type*} [Fintype ι] [Fintype κ] [Fintype δ]
    (p : ι → ℝ) (q : κ → ℝ) (A : ι → δ → ℝ) (B : κ → δ → ℝ) :
    (∑ k, (∑ i, p i*A i k)*(∑ j, q j*B j k))=
      ∑ i, ∑ j, p i*q j*(∑ k, A i k*B j k) := by
  simp only [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

end ProductCovariance
open scoped BigOperators

namespace ProductTransport

theorem covariance_transport_bound {ι : Type*} [Fintype ι]
    (w x h K : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hx : ∀ i, 0 ≤ x i)
    (hw1 : ∑ i, w i = 1) (hh0 : ∑ i, w i*h i = 0)
    (hcenter : ∑ i, w i*x i*h i = ∑ i, w i*K i*h i) :
    1 + (∑ i, w i*x i) - (∑ i, w i*(K i)^2) ≤
      ∑ i, w i*(1+x i)*(1+h i)^2 := by
  have hn : 0 ≤ ∑ i, w i*(x i*(h i)^2+(h i+K i)^2) := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hw i) (add_nonneg (mul_nonneg (hx i) (sq_nonneg _))
      (sq_nonneg _))
  have heq : (∑ i, w i*(x i*(h i)^2+(h i+K i)^2)) =
      (∑ i, w i*(1+x i)*(1+h i)^2) - (∑ i, w i) -
      (∑ i, w i*x i) - 2*(∑ i, w i*h i) -
      2*(∑ i, w i*x i*h i) + 2*(∑ i, w i*K i*h i) +
      (∑ i, w i*(K i)^2) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq, hw1, hh0, hcenter] at hn
  linarith

theorem rational_transport_bound {ι : Type*} [Fintype ι]
    (w x h : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1)
    (hw1 : ∑ i, w i = 1) (hh0 : ∑ i, w i*h i = 0) :
    (∑ i, w i*x i) ≤ (2-(∑ i, w i*x i))*
      ((∑ i, w i*(1+x i)*(1+h i)^2)-1) := by
  have hd (i : ι) : 0 < 1+x i := by linarith [hx0 i]
  have hA : 0 ≤ ∑ i, w i*(1+x i)*(1+h i)^2 := by
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hw i) (hd i).le) (sq_nonneg _)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := Finset.univ)
    (r := fun i => w i*(1+h i))
    (f := fun i => w i*(1+x i)*(1+h i)^2)
    (g := fun i => w i/(1+x i))
    (fun i _ => mul_nonneg (mul_nonneg (hw i) (hd i).le) (sq_nonneg _))
    (fun i _ => div_nonneg (hw i) (hd i).le)
    (fun i _ => by
      have hd0 := (hd i).ne'
      field_simp
      nlinarith [sq_nonneg (w i*(1+h i))])
  have hsum : (∑ i, w i*(1+h i)) = 1 := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hw1, hh0, add_zero]
  rw [hsum] at hcs
  have hb : (∑ i, w i/(1+x i)) ≤ 1-(∑ i, w i*x i)/2 := by
    calc
      _ ≤ ∑ i, w i*(1-x i/2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (hw i)
        rw [← one_div]
        apply (div_le_iff₀ (hd i)).2
        have hp := mul_nonneg (hx0 i) (sub_nonneg.mpr (hx1 i))
        nlinarith
      _ = _ := by
        simp only [mul_sub, mul_one, ← mul_div_assoc, Finset.sum_sub_distrib,
          ← Finset.sum_div, hw1]
  have hh := mul_le_mul_of_nonneg_left hb hA
  nlinarith

end ProductTransport

open scoped BigOperators
namespace FourBasisScalar

def pairIndex : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

theorem pairIndex_lt (i : Fin 6) : (pairIndex i).1 < (pairIndex i).2 := by
  fin_cases i <;> decide

def pairValues (f : Fin 4 → Fin 4 → ℝ) (i : Fin 6) : ℝ :=
  f (pairIndex i).1 (pairIndex i).2

theorem pair_sum (f : Fin 4 → Fin 4 → ℝ) :
    (∑ i, pairValues f i) = ∑ a, ∑ b, if a<b then f a b else 0 := by
  simp only [Fin.sum_univ_four]
  norm_num [pairValues, pairIndex, Fin.sum_univ_succ, Fin.lt_def]
  ring

theorem six_rational_aggregate (z e : Fin 6 → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1)
    (he : ∀ i, z i ≤ (2-z i)*e i) :
    6*(∑ i, z i) ≤ (12-(∑ i, z i))*(∑ i, e i) := by
  have he0 (i : Fin 6) : 0 ≤ e i := by
    have hden : 0 < 2-z i := by linarith [hz1 i]
    exact nonneg_of_mul_nonneg_right ((hz0 i).trans (he i)) hden
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s:=Finset.univ) (r:=fun _ : Fin 6 => (1:ℝ))
    (f:=fun i => 2-z i) (g:=fun i => (e i+1)/2)
    (fun i _ => by linarith [hz1 i])
    (fun i _ => div_nonneg (by linarith [he0 i]) (by norm_num))
    (fun i _ => by nlinarith [he i])
  have hf : (∑ i, (2-z i)) = 12-(∑ i, z i) := by norm_num [Finset.sum_sub_distrib]
  have hg : (∑ i, (e i+1)/2) = ((∑ i, e i)+6)/2 := by
    simp [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hf,hg] at h
  norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  nlinarith

theorem pair_product_bound (u : Fin 4 → ℝ) :
    8*(∑ i, pairValues (fun a b => u a*u b) i) ≤ 3*(∑ a, u a)^2 := by
  have h : 8*(u 0*u 1+u 0*u 2+u 0*u 3+u 1*u 2+u 1*u 3+u 2*u 3) ≤
      3*(u 0+u 1+u 2+u 3)^2 := by
    nlinarith [sq_nonneg (u 0-u 1), sq_nonneg (u 0-u 2), sq_nonneg (u 0-u 3),
      sq_nonneg (u 1-u 2), sq_nonneg (u 1-u 3), sq_nonneg (u 2-u 3)]
  simpa [pairValues,pairIndex,Fin.sum_univ_succ,add_assoc] using h

theorem four_pair_optimum (u : Fin 4 → ℝ) (z e : Fin 4 → Fin 4 → ℝ)
    (hu : ∀ a, 0 ≤ u a)
    (hz0 : ∀ a b, a<b → 0 ≤ z a b) (hz1 : ∀ a b, a<b → z a b ≤ 1)
    (hlow : ∀ a b, a<b → z a b-u a*u b ≤ e a b)
    (hrat : ∀ a b, a<b → z a b ≤ (2-z a b)*e a b)
    (hframe : 2/3+(∑ a, u a)/2 ≤ ∑ a, ∑ b, if a<b then z a b else 0) :
    2/3 ≤ ∑ a, ∑ b, if a<b then e a b else 0 := by
  let U := ∑ a, u a
  let Z := ∑ i, pairValues z i
  let E := ∑ i, pairValues e i
  have hU : 0 ≤ U := Finset.sum_nonneg fun a _ => hu a
  have hZ : Z ≤ 6 := by
    calc
      _ ≤ ∑ _i : Fin 6, (1:ℝ) := Finset.sum_le_sum fun i _ =>
        hz1 _ _ (pairIndex_lt i)
      _ = 6 := by norm_num
  have hF : 2/3+U/2 ≤ Z := by simpa only [Z,U,pair_sum] using hframe
  have hE : Z-(∑ i, pairValues (fun a b => u a*u b) i) ≤ E := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => hlow _ _ (pairIndex_lt i)
  have hprod := pair_product_bound u
  have hR : 6*Z ≤ (12-Z)*E := six_rational_aggregate (pairValues z) (pairValues e)
    (fun i => hz0 _ _ (pairIndex_lt i)) (fun i => hz1 _ _ (pairIndex_lt i))
    (fun i => hrat _ _ (pairIndex_lt i))
  have hroot : 2/3 ≤ E := by
    by_cases hh : U ≤ 4/3
    · have hp := mul_nonneg hU (sub_nonneg.mpr hh)
      change 8*_ ≤ 3*U^2 at hprod
      nlinarith
    · have hzz : 4/3 < Z := by linarith
      by_contra he
      have he' : E < 2/3 := lt_of_not_ge he
      have hm := mul_pos (show 0 < 12-Z by linarith) (sub_pos.mpr he')
      nlinarith
  simpa only [E,pair_sum] using hroot

end FourBasisScalar

namespace ProductPhysicalTransport
open ProductGeometry ProductCoarseGraining ProductCovariance ProductTransport

def axisVector (P : NormalizedProductBasis) (i : Fin 6) (k : Fin 3 × Fin 3) : ℝ :=
  P.b i k.1*P.b i k.2
def frameMean (P : NormalizedProductBasis) (k : Fin 3 × Fin 3) : ℝ :=
  ∑ i, (1/6:ℝ)*axisVector P i k
def impurity (P : NormalizedProductBasis) : ℝ := 1-∑ k, (frameMean P k)^2
def frameCross (P Q : NormalizedProductBasis) : ℝ := ∑ k, frameMean P k*frameMean Q k
def pairError (P Q : NormalizedProductBasis) : ℝ :=
  (∑ i, ∑ j, (productTransition P Q i j)^2)-1
def centeredCross (P Q : NormalizedProductBasis) (i j : Fin 6) : ℝ :=
  ∑ k, (axisVector P i k-frameMean P k)*(axisVector Q j k-frameMean Q k)

theorem bloch_unit (P : NormalizedProductBasis) (i : Fin 6) :
    (∑ t, (P.b i t)^2)=1 := by
  change (∑ t, (bloch (P.u i) t)^2)=1
  rw [bloch_norm,P.hu]
  norm_num

theorem axis_unit (P : NormalizedProductBasis) (i : Fin 6) :
    (∑ k, (axisVector P i k)^2)=1 := by
  unfold axisVector
  rw [outer_norm,bloch_unit]
  norm_num

theorem impurity_variance (P : NormalizedProductBasis) :
    (∑ i, (1/6:ℝ)*(∑ k, (axisVector P i k-frameMean P k)^2))=impurity P := by
  have hh := vector_weighted_variance (fun _ : Fin 6 => (1/6:ℝ))
    (axisVector P) (frameMean P) (by norm_num) (fun _ => rfl)
  simp_rw [axis_unit] at hh
  simpa [impurity] using hh

theorem impurity_nonneg (P : NormalizedProductBasis) : 0 ≤ impurity P := by
  rw [←impurity_variance]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun k _ => sq_nonneg _)

theorem frameCross_mean (P Q : NormalizedProductBasis) :
    frameCross P Q=∑ i, ∑ j, (1/36:ℝ)*(∑ t, P.b i t*Q.b j t)^2 := by
  unfold frameCross frameMean
  rw [mean_inner]
  simp only [axisVector,outer_inner]
  norm_num

theorem bloch_dot_sq_le_one (P Q : NormalizedProductBasis) (i j : Fin 6) :
    (∑ t, P.b i t*Q.b j t)^2≤1 := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (P.b i) (Q.b j)
  simpa only [bloch_unit,one_mul] using hh

theorem frameCross_bounds (P Q : NormalizedProductBasis) :
    0≤frameCross P Q ∧ frameCross P Q≤1 := by
  rw [frameCross_mean]
  constructor
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (by norm_num) (sq_nonneg _)
  · calc
      _ ≤ ∑ _i : Fin 6, ∑ _j : Fin 6, (1/36:ℝ)*1 := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (bloch_dot_sq_le_one P Q i j) (by norm_num)
      _ = 1 := by norm_num

theorem transport_centered_row (P Q : NormalizedProductBasis) (i : Fin 6) :
    (∑ j, (1/6:ℝ)*(transportH P Q i j-1))=0 := by
  rw [←Finset.mul_sum,Finset.sum_sub_distrib,transportH_row]
  norm_num

theorem transport_centered_col (P Q : NormalizedProductBasis) (j : Fin 6) :
    (∑ i, (1/6:ℝ)*(transportH P Q i j-1))=0 := by
  rw [←Finset.mul_sum,Finset.sum_sub_distrib,transportH_col]
  norm_num

theorem transport_centered_mean (P Q : NormalizedProductBasis) :
    (∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(transportH P Q ij.1 ij.2-1))=0 := by
  rw [Fintype.sum_prod_type]
  have hh (i : Fin 6) :
      (∑ j, (1/36:ℝ)*(transportH P Q i j-1))=(1/6:ℝ)*
        (∑ j, (1/6:ℝ)*(transportH P Q i j-1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [hh,transport_centered_row,mul_zero,Finset.sum_const_zero]

theorem centeredCross_variance_bound (P Q : NormalizedProductBasis) :
    (∑ i, ∑ j, (1/36:ℝ)*(centeredCross P Q i j)^2) ≤ impurity P*impurity Q := by
  have hh := weighted_covariance_cauchy (fun _ : Fin 6 => (1/6:ℝ))
    (fun _ : Fin 6 => (1/6:ℝ))
    (fun i k => axisVector P i k-frameMean P k)
    (fun j k => axisVector Q j k-frameMean Q k)
    (fun _ => by norm_num) (fun _ => by norm_num)
  rw [impurity_variance,impurity_variance] at hh
  norm_num only [show (1/6:ℝ)*(1/6)=1/36 by norm_num] at hh
  exact hh

def transportFrame (P Q : NormalizedProductBasis) : ℝ :=
  ∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(1+(∑ t, P.b ij.1 t*Q.b ij.2 t)^2)*
    (transportH P Q ij.1 ij.2)^2

theorem transportFrame_le (P Q : NormalizedProductBasis) :
    transportFrame P Q≤pairError P Q+1 := by
  have hh := actual_product_transport_bound P Q
  have heq : transportFrame P Q=(1/36:ℝ)*
      (∑ i, ∑ j, (1+(∑ t, P.b i t*Q.b j t)^2)*(transportH P Q i j)^2) := by
    unfold transportFrame
    rw [Fintype.sum_prod_type]
    simp only [Finset.mul_sum,mul_assoc]
  rw [←heq] at hh
  simpa only [pairError,sub_add_cancel] using hh

theorem covariance_centering (P Q : NormalizedProductBasis) :
    (∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(∑ t, P.b ij.1 t*Q.b ij.2 t)^2*
      (transportH P Q ij.1 ij.2-1)) =
    ∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*centeredCross P Q ij.1 ij.2*
      (transportH P Q ij.1 ij.2-1) := by
  have hh := vector_transport_centering (fun _ : Fin 6 => (1/6:ℝ))
    (fun _ : Fin 6 => (1/6:ℝ)) (axisVector P) (axisVector Q)
    (frameMean P) (frameMean Q) (fun i j => transportH P Q i j-1)
    (transport_centered_row P Q) (transport_centered_col P Q)
  norm_num only [show (1/6:ℝ)*(1/6)=1/36 by norm_num] at hh
  simp only [Fintype.sum_prod_type]
  change (∑ i, ∑ j, (1/36:ℝ)*centeredCross P Q i j*(transportH P Q i j-1))=
    (∑ i, ∑ j, (1/36:ℝ)*(∑ k, axisVector P i k*axisVector Q j k)*
      (transportH P Q i j-1)) at hh
  simpa only [axisVector,outer_inner] using hh.symm

theorem actual_pair_low_bound (P Q : NormalizedProductBasis) :
    frameCross P Q-impurity P*impurity Q≤pairError P Q := by
  have hh := covariance_transport_bound (fun _ : Fin 6 × Fin 6 => (1/36:ℝ))
    (fun ij => (∑ t, P.b ij.1 t*Q.b ij.2 t)^2)
    (fun ij => transportH P Q ij.1 ij.2-1)
    (fun ij => centeredCross P Q ij.1 ij.2)
    (fun _ => by norm_num) (fun _ => sq_nonneg _)
    (by norm_num) (transport_centered_mean P Q) (covariance_centering P Q)
  have hz : (∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(∑ t, P.b ij.1 t*Q.b ij.2 t)^2)=
      frameCross P Q := by rw [Fintype.sum_prod_type,frameCross_mean]
  rw [hz] at hh
  simp only [show ∀ t : ℝ, 1+(t-1)=t from fun t => by ring] at hh
  change 1+frameCross P Q-
    (∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(centeredCross P Q ij.1 ij.2)^2)≤
      transportFrame P Q at hh
  have hv := centeredCross_variance_bound P Q
  rw [Fintype.sum_prod_type] at hh
  have ht := transportFrame_le P Q
  linarith

theorem actual_pair_rational_bound (P Q : NormalizedProductBasis) :
    frameCross P Q≤(2-frameCross P Q)*pairError P Q := by
  have hh := rational_transport_bound (fun _ : Fin 6 × Fin 6 => (1/36:ℝ))
    (fun ij => (∑ t, P.b ij.1 t*Q.b ij.2 t)^2)
    (fun ij => transportH P Q ij.1 ij.2-1)
    (fun _ => by norm_num) (fun _ => sq_nonneg _)
    (fun ij => bloch_dot_sq_le_one P Q ij.1 ij.2)
    (by norm_num) (transport_centered_mean P Q)
  have hz : (∑ ij : Fin 6 × Fin 6, (1/36:ℝ)*(∑ t, P.b ij.1 t*Q.b ij.2 t)^2)=
      frameCross P Q := by rw [Fintype.sum_prod_type,frameCross_mean]
  rw [hz] at hh
  simp only [show ∀ t : ℝ, 1+(t-1)=t from fun t => by ring] at hh
  change frameCross P Q≤(2-frameCross P Q)*(transportFrame P Q-1) at hh
  have ht := transportFrame_le P Q
  have hb := (frameCross_bounds P Q).2
  nlinarith [mul_nonneg (show 0≤2-frameCross P Q by linarith)
    (show 0≤pairError P Q+1-transportFrame P Q by linarith)]

theorem frameMean_trace (P : NormalizedProductBasis) :
    (∑ t, frameMean P (t,t))=1 := by
  unfold frameMean axisVector
  rw [Finset.sum_comm]
  simp only [←sq,←Finset.mul_sum,bloch_unit,mul_one]
  norm_num

theorem four_physical_frame_bound (P : Fin 4 → NormalizedProductBasis) :
    2/3+(∑ a, impurity (P a))/2 ≤
      ∑ a, ∑ b, if a<b then frameCross (P a) (P b) else 0 := by
  have hh := four_trace_frame_bound (fun a i j => frameMean (P a) (i,j))
    (fun a => frameMean_trace (P a))
  simpa only [impurity,frameCross,Fintype.sum_prod_type] using hh

theorem four_normalized_product_lower_bound (P : Fin 4 → NormalizedProductBasis) :
    (2:ℝ)/3 ≤ ∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0 := by
  apply FourBasisScalar.four_pair_optimum (fun a => impurity (P a))
    (fun a b => frameCross (P a) (P b)) (fun a b => pairError (P a) (P b))
  · exact fun a => impurity_nonneg (P a)
  · exact fun a b _ => (frameCross_bounds (P a) (P b)).1
  · exact fun a b _ => (frameCross_bounds (P a) (P b)).2
  · exact fun a b _ => actual_pair_low_bound (P a) (P b)
  · exact fun a b _ => actual_pair_rational_bound (P a) (P b)
  · exact four_physical_frame_bound P

theorem zero_impurity_axes_coincide (P : NormalizedProductBasis) (h : impurity P=0)
    (i j : Fin 6) : axisVector P i=axisVector P j := by
  have hv := impurity_variance P
  rw [h] at hv
  have hv0 (i : Fin 6) : (1/6:ℝ)*(∑ k, (axisVector P i k-frameMean P k)^2)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun k _ => sq_nonneg _))).mp hv i (Finset.mem_univ i)
  have hmean (i : Fin 6) (k : Fin 3 × Fin 3) : axisVector P i k=frameMean P k := by
    have hs : (∑ k, (axisVector P i k-frameMean P k)^2)=0 :=
      (mul_eq_zero.mp (hv0 i)).resolve_left (by norm_num)
    have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
      sq_nonneg (axisVector P i k-frameMean P k))).mp hs k (Finset.mem_univ k)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hk)
  funext k
  rw [hmean i k,hmean j k]

end ProductPhysicalTransport
open scoped BigOperators ComplexConjugate

namespace ProductParseval

theorem resolution_parseval {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (v : ι → κ → ℂ) (w : κ → ℂ)
    (hres : ∀ k l, (∑ i, v i k*star (v i l))=if k=l then 1 else 0) :
    (∑ i, Complex.normSq (∑ k, star (w k)*v i k))=∑ k, Complex.normSq (w k) := by
  apply Complex.ofReal_injective
  push_cast
  have he (i : ι) :
      (Complex.normSq (∑ k, star (w k)*v i k) : ℂ)=
        ∑ k, ∑ l, (star (w k)*w l)*(v i k*star (v i l)) := by
    rw [← Complex.mul_conj]
    simp only [map_sum, map_mul, starRingEnd_apply, star_star]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hres]
  simp [Complex.normSq_eq_conj_mul_self]

end ProductParseval
namespace ProductPhysicalTransport
open scoped BigOperators

theorem productTransition_row_sum (P Q : NormalizedProductBasis) (i : Fin 6) :
    (∑ j, productTransition P Q i j)=1 := by
  have h := ProductParseval.resolution_parseval
    (fun j (k : Fin 2 × Fin 3) => Q.u j k.1*Q.v j k.2)
    (fun (k : Fin 2 × Fin 3) => P.u i k.1*P.v i k.2)
    (fun k l => by simpa only [Prod.ext_iff] using Q.hres k.1 l.1 k.2 l.2)
  simp only [Fintype.sum_prod_type] at h
  change (∑ j, productTransition P Q i j)=_ at h
  rw [h]
  simp only [Complex.normSq_mul, ← Finset.mul_sum, ← Finset.sum_mul, P.hu, P.hv, mul_one]

theorem productTransition_total (P Q : NormalizedProductBasis) :
    (∑ i, ∑ j, productTransition P Q i j)=6 := by
  simp only [productTransition_row_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_ofNat]

theorem pairError_eq_centered_squares (P Q : NormalizedProductBasis) :
    pairError P Q=(∑ i, ∑ j, (productTransition P Q i j-1/6)^2) := by
  have he (x : ℝ) : (x-1/6)^2=x^2-(1/3)*x+1/36 := by ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [productTransition_total]
  unfold pairError
  ring

theorem pairError_nonneg (P Q : NormalizedProductBasis) : 0 ≤ pairError P Q := by
  rw [pairError_eq_centered_squares]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

end ProductPhysicalTransport

/-- Every four orthonormal product bases in C² ⊗ C³ have total squared
    transition-probability error at least 2/3. -/
theorem four_product_energy_lower_bound
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j,
      productBasisInner B a a i j = if i = j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y = u x * v y) :
    (2:ℝ)/3 ≤ productBasisEnergy B := by
  have ho : ∀ a i j, productBasisInner B a a i j=
      @ite ℂ (i=j) (Classical.propDecidable (i=j)) 1 0 := by
    intro a i j
    by_cases h : i=j
    · simpa only [if_pos h] using horth a i j
    · simpa only [if_neg h] using horth a i j
  obtain ⟨P,hP⟩ := ProductPhysicalTransport.normalized_bases_from_raw B ho hproduct
  have ht (a b : Fin 4) (i j : Fin 6) :
      ProductPhysicalTransport.productTransition (P a) (P b) i j=
      Complex.normSq (productBasisInner B a b i j) := by
    unfold ProductPhysicalTransport.productTransition productBasisInner
    simp_rw [hP]
  have hh := ProductPhysicalTransport.four_normalized_product_lower_bound P
  simpa only [ProductPhysicalTransport.pairError_eq_centered_squares,ht,
    productBasisEnergy] using hh

end
end
end

section

/-! Explicit four product bases in dimension six attaining total squared
unbiasedness error 2/3. This construction is the attainment half of the sharp
product-basis optimization theorem; it does not prove its universal lower bound.
The quantitative optimization strengthens the exact-unbiasedness exclusion in
McNulty--Weigert, All Mutually Unbiased Product Bases in Dimension Six (2012).
-/
open scoped BigOperators Matrix Kronecker ComplexConjugate
noncomputable section
namespace TetrahedralProductBases

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ
abbrev M6 := Matrix (Fin 2 × Fin 3) (Fin 2 × Fin 3) ℂ

def w : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩
def wb : ℂ := ⟨-1 / 2, -(Real.sqrt 3 / 2)⟩

def A3 : M3 := fun i j => (Real.sqrt 3 / 3 : ℝ) *
  (!![1, 1, 1; 1, w, wb; 1, wb, w] : M3) i j
def C3 : M3 := fun i j => (Real.sqrt 3 / 3 : ℝ) *
  (!![1, 1, 1; w, wb, 1; w, 1, wb] : M3) i j
def D3 : M3 := fun i j => (Real.sqrt 3 / 3 : ℝ) *
  (!![1, 1, 1; wb, w, 1; wb, 1, w] : M3) i j
def qutrit : Fin 4 → M3 := ![1, A3, C3, D3]

lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
lemma sqrt_two_sq : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
lemma sqrt_three_cube : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
  rw [pow_succ, sqrt_three_sq]
lemma sqrt_three_four : Real.sqrt 3 ^ 4 = (9 : ℝ) := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_three_six : Real.sqrt 3 ^ 6 = (27 : ℝ) := by
  rw [show (6 : ℕ) = 2 * 3 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_three_eight : Real.sqrt 3 ^ 8 = (81 : ℝ) := by
  rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_two_four : Real.sqrt 2 ^ 4 = (4 : ℝ) := by
  rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sqrt_two_sq]; norm_num
lemma sqrt_two_six : Real.sqrt 2 ^ 6 = (8 : ℝ) := by
  calc
    _ = (Real.sqrt 2 ^ 2)^3 := by ring
    _ = (8:ℝ) := by rw [sqrt_two_sq]; norm_num
lemma sqrt_two_eight : Real.sqrt 2 ^ 8 = (16 : ℝ) := by
  rw [show (8 : ℕ) = 2 * 4 by rfl, pow_mul, sqrt_two_sq]; norm_num
lemma sqrt_three_ten : Real.sqrt 3 ^ 10 = (243 : ℝ) := by
  rw [show (10 : ℕ) = 2 * 5 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_three_twelve : Real.sqrt 3 ^ 12 = (729 : ℝ) := by
  rw [show (12 : ℕ) = 2 * 6 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_three_fourteen : Real.sqrt 3 ^ 14 = (2187 : ℝ) := by
  rw [show (14 : ℕ) = 2 * 7 by rfl, pow_mul, sqrt_three_sq]; norm_num
lemma sqrt_three_sixteen : Real.sqrt 3 ^ 16 = (6561 : ℝ) := by
  rw [show (16 : ℕ) = 2 * 8 by rfl, pow_mul, sqrt_three_sq]; norm_num

set_option maxHeartbeats 4000000 in
theorem qutrit_unitary (r : Fin 4) : (qutrit r)ᴴ * qutrit r = 1 := by
  fin_cases r
  · simp [qutrit]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext
      <;> norm_num [qutrit, A3, C3, D3, w, wb, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      <;> ring_nf
      <;> norm_num [sqrt_three_sq, sqrt_three_cube, sqrt_three_four]

set_option maxHeartbeats 4000000 in
theorem qutrit_unbiased (r s : Fin 4) (hrs : r < s) (i j : Fin 3) :
    Complex.normSq (((qutrit r)ᴴ * qutrit s) i j) = (1 : ℝ)/3 := by
  fin_cases r <;> fin_cases s <;> norm_num at hrs
  all_goals
    dsimp [qutrit]
    try simp only [Matrix.conjTranspose_one, Matrix.one_mul]
    fin_cases i <;> fin_cases j
      <;> norm_num [A3, C3, D3, w, wb, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      <;> ring_nf
      <;> norm_num [sqrt_three_sq, sqrt_three_cube, sqrt_three_four,
        sqrt_three_six, sqrt_three_eight]

def qubitMatrix (z : ℂ) : M2 := fun i j => (Real.sqrt 3 / 3 : ℝ) *
  (!![1, -(Real.sqrt 2 : ℂ) * star z; (Real.sqrt 2 : ℂ) * z, 1] : M2) i j
def qubit : Fin 4 → M2 := ![1, qubitMatrix 1, qubitMatrix w, qubitMatrix wb]

set_option maxHeartbeats 4000000 in
theorem qubit_unitary (r : Fin 4) : (qubit r)ᴴ * qubit r = 1 := by
  fin_cases r
  · simp [qubit]
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext
      <;> norm_num [qubit, qubitMatrix, w, wb, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      <;> ring_nf
      <;> norm_num [sqrt_three_sq, sqrt_three_cube, sqrt_three_four, sqrt_two_sq]

set_option maxHeartbeats 8000000 in
theorem qubit_entry_error (r s : Fin 4) (hrs : r < s) (i j : Fin 2) :
    (Complex.normSq (((qubit r)ᴴ * qubit s) i j) - (1:ℝ)/2)^2 = 1/36 := by
  fin_cases r <;> fin_cases s <;> norm_num at hrs
  all_goals
    dsimp [qubit]
    try simp only [Matrix.conjTranspose_one, Matrix.one_mul]
    fin_cases i <;> fin_cases j
      <;> norm_num [qubitMatrix, w, wb, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fin.sum_univ_succ, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.conj_re, Complex.conj_im]
      <;> ring_nf
      <;> norm_num [sqrt_three_sq, sqrt_three_cube, sqrt_three_four,
        sqrt_three_six, sqrt_three_eight, sqrt_two_sq, sqrt_two_four,
        sqrt_two_six, sqrt_two_eight, sqrt_three_ten, sqrt_three_twelve,
        sqrt_three_fourteen, sqrt_three_sixteen]

def productBasis (r : Fin 4) : M6 := qubit r ⊗ₖ qutrit r

theorem product_gram (r s : Fin 4) :
    (productBasis r)ᴴ * productBasis s =
      ((qubit r)ᴴ * qubit s) ⊗ₖ ((qutrit r)ᴴ * qutrit s) := by
  rw [productBasis, productBasis, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]

theorem product_unitary (r : Fin 4) : (productBasis r)ᴴ * productBasis r = 1 := by
  rw [product_gram, qubit_unitary, qutrit_unitary, Matrix.one_kronecker_one]

theorem product_entry_error (r s : Fin 4) (hrs : r < s)
    (i j : Fin 2 × Fin 3) :
    (Complex.normSq (((productBasis r)ᴴ * productBasis s) i j) - (1:ℝ)/6)^2 =
      1/324 := by
  rw [product_gram]
  change (Complex.normSq (_ * _) - (1:ℝ)/6)^2 = 1/324
  rw [Complex.normSq_mul, qutrit_unbiased r s hrs]
  have h := qubit_entry_error r s hrs i.1 j.1
  nlinarith

def totalError (B : Fin 4 → M6) : ℝ := ∑ r, ∑ s,
  if r < s then ∑ i, ∑ j, (Complex.normSq (((B r)ᴴ * B s) i j) - 1/6)^2 else 0

theorem product_total_error : totalError productBasis = (2:ℝ)/3 := by
  unfold totalError
  have h (r s : Fin 4) (hrs : r < s) :
      (∑ i, ∑ j, (Complex.normSq (((productBasis r)ᴴ * productBasis s) i j) - 1/6)^2) =
        (1:ℝ)/9 := by
    calc
      _ = ∑ _i : Fin 2 × Fin 3, ∑ _j : Fin 2 × Fin 3, (1:ℝ)/324 := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact product_entry_error r s hrs i j
      _ = (1:ℝ)/9 := by norm_num
  have he (r s : Fin 4) :
      (if r < s then ∑ i, ∑ j,
        (Complex.normSq (((productBasis r)ᴴ * productBasis s) i j) - 1/6)^2 else 0) =
      (if r < s then (1:ℝ)/9 else 0) := by
    split_ifs with hrs
    · exact h r s hrs
    · rfl
  simp_rw [he]
  norm_num [Fin.sum_univ_succ]
  norm_num [show (0 : Fin 4) < 2 by decide, show (1 : Fin 4) < 2 by decide,
    show ¬ (Fin.succ (2 : Fin 3) < (2 : Fin 4)) by decide,
    show (0 : Fin 3) < 2 by decide, show (1 : Fin 3) < 2 by decide]

def indexEquiv : Fin 6 ≃ Fin 2 × Fin 3 := (@finProdFinEquiv 2 3).symm

def rawBasis (r : Fin 4) (i : Fin 6) (x : Fin 2) (y : Fin 3) : ℂ :=
  productBasis r (x,y) (indexEquiv i)

def rawInner (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (r s : Fin 4) (i j : Fin 6) : ℂ :=
  ∑ x, ∑ y, star (B r i x y) * B s j x y

def rawEnergy (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ) : ℝ :=
  ∑ r, ∑ s, if r < s then ∑ i, ∑ j,
    (Complex.normSq (rawInner B r s i j) - 1/6)^2 else 0

theorem raw_inner (r s : Fin 4) (i j : Fin 6) :
    rawInner rawBasis r s i j =
      ((productBasis r)ᴴ * productBasis s) (indexEquiv i) (indexEquiv j) := by
  simp only [rawInner,rawBasis,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]

theorem raw_orthonormal (r : Fin 4) (i j : Fin 6) :
    rawInner rawBasis r r i j = if i=j then 1 else 0 := by
  rw [raw_inner,product_unitary]
  simp [Matrix.one_apply,indexEquiv.injective.eq_iff]

theorem raw_product (r : Fin 4) (i : Fin 6) :
    ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ), ∀ x y, rawBasis r i x y = u x * v y := by
  exact ⟨fun x => qubit r x (indexEquiv i).1,
    fun y => qutrit r y (indexEquiv i).2, fun _ _ => rfl⟩

theorem raw_energy : rawEnergy rawBasis = (2:ℝ)/3 := by
  have he : rawEnergy rawBasis = totalError productBasis := by
    unfold rawEnergy totalError
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    split_ifs
    · simp_rw [raw_inner]
      rw [show (∑ i : Fin 6, ∑ j : Fin 6,
        (Complex.normSq (((productBasis r)ᴴ * productBasis s) (indexEquiv i)
          (indexEquiv j)) - 1/6)^2) =
        (∑ i : Fin 2 × Fin 3, ∑ j : Fin 6,
        (Complex.normSq (((productBasis r)ᴴ * productBasis s) i
          (indexEquiv j)) - 1/6)^2) from
            Fintype.sum_equiv indexEquiv _ _ (fun _ => rfl)]
      apply Finset.sum_congr rfl
      intro i _
      exact Fintype.sum_equiv indexEquiv _ _ (fun _ => rfl)
    · rfl
  exact he.trans product_total_error

theorem product_basis_attainment :
    ∃ B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ,
      (∀ r i j, rawInner B r r i j = if i=j then 1 else 0) ∧
      (∀ r i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ), ∀ x y, B r i x y = u x * v y) ∧
      rawEnergy B = (2:ℝ)/3 :=
  ⟨rawBasis, raw_orthonormal, raw_product, raw_energy⟩


theorem raw_entry_error (r s : Fin 4) (hrs : r<s) (i j : Fin 6) :
    (Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6)^2 = 1/324 := by
  rw [raw_inner]
  exact product_entry_error r s hrs _ _

theorem raw_entry_absolute_error (r s : Fin 4) (hrs : r<s) (i j : Fin 6) :
    |Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6| = 1/18 := by
  have hs := raw_entry_error r s hrs i j
  have ha := sq_abs (Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6)
  have hn := abs_nonneg (Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6)
  nlinarith

theorem raw_pair_energy (r s : Fin 4) (hrs : r<s) :
    (∑ i : Fin 6, ∑ j : Fin 6,
      (Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6)^2) = 1/9 := by
  simp_rw [raw_entry_error r s hrs]
  norm_num

theorem raw_pair_distance (r s : Fin 4) (hrs : r<s) :
    1 - (∑ i : Fin 6, ∑ j : Fin 6,
      (Complex.normSq (rawInner rawBasis r s i j)-(1:ℝ)/6)^2)/5 = 44/45 := by
  rw [raw_pair_energy r s hrs]
  norm_num

end TetrahedralProductBases

end
end

section
namespace ProductMinimax
open FourBasisScalar

theorem pair_lower_of_total (e : Fin 4 → Fin 4 → ℝ)
    (ht : (2:ℝ)/3 ≤ ∑ a, ∑ b, if a<b then e a b else 0) :
    ∃ a b : Fin 4, a<b ∧ 1/9 ≤ e a b := by
  classical
  by_contra hn
  have hlt (i : Fin 6) : pairValues e i < 1/9 := by
    apply lt_of_not_ge
    intro h
    exact hn ⟨_,_,pairIndex_lt i,h⟩
  have hs := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    (fun (i : Fin 6) _ => hlt i)
  rw [pair_sum] at hs
  norm_num at hs
  linarith

theorem entry_lower_of_total (e : Fin 4 → Fin 4 → Fin 6 → Fin 6 → ℝ)
    (ht : (2:ℝ)/3 ≤ ∑ a, ∑ b, if a<b then ∑ i, ∑ j, (e a b i j)^2 else 0) :
    ∃ a b : Fin 4, ∃ i j : Fin 6, a<b ∧ 1/18 ≤ |e a b i j| := by
  classical
  by_contra hn
  have hlt (k i j : Fin 6) : (e (pairIndex k).1 (pairIndex k).2 i j)^2 < 1/324 := by
    have ha : |e (pairIndex k).1 (pairIndex k).2 i j| < 1/18 := by
      apply lt_of_not_ge
      intro h
      exact hn ⟨_,_,i,j,pairIndex_lt k,h⟩
    have hb := abs_nonneg (e (pairIndex k).1 (pairIndex k).2 i j)
    have hc := sq_abs (e (pairIndex k).1 (pairIndex k).2 i j)
    nlinarith
  have hs : (∑ k : Fin 6, ∑ i : Fin 6, ∑ j : Fin 6,
      (e (pairIndex k).1 (pairIndex k).2 i j)^2) <
      ∑ _k : Fin 6, ∑ _i : Fin 6, ∑ _j : Fin 6, (1:ℝ)/324 := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro k _
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hlt k i j)
  change (∑ k : Fin 6, pairValues (fun a b => ∑ i, ∑ j, (e a b i j)^2) k) < _ at hs
  rw [pair_sum] at hs
  norm_num at hs
  linarith

theorem mean_distance_upper_of_total (e : Fin 4 → Fin 4 → ℝ)
    (ht : (2:ℝ)/3 ≤ ∑ a, ∑ b, if a<b then e a b else 0) :
    (∑ a, ∑ b, if a<b then 1-e a b/5 else 0)/6 ≤ 44/45 := by
  rw [← pair_sum] at ht ⊢
  have hs : (∑ i, pairValues (fun a b => 1-e a b/5) i) =
      6 - (∑ i, pairValues e i)/5 := by
    simp only [pairValues, Finset.sum_sub_distrib, ← Finset.sum_div]
    norm_num
  rw [hs]
  linarith

theorem worst_pair_distance_upper_of_total (e : Fin 4 → Fin 4 → ℝ)
    (ht : (2:ℝ)/3 ≤ ∑ a, ∑ b, if a<b then e a b else 0) :
    ∃ a b : Fin 4, a<b ∧ 1-e a b/5 ≤ 44/45 := by
  obtain ⟨a,b,hab,h⟩ := pair_lower_of_total e ht
  exact ⟨a,b,hab,by linarith⟩
end ProductMinimax



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

theorem triple_resolvent_gap (P Q R : PVM n D) (hn : 2≤n)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam) :
    ∃ g : ℝ, 0<g ∧ ∀ abc, g • (1:M) ≤ lam • 1-tripleSum P Q R abc := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  obtain ⟨hs,hsb,hsq⟩ := SpectralPolynomialBounds.inverse_sqrt_bounds (n:ℝ) hnR
  have hl := (SpectralPolynomialBounds.original_root_estimates (n:ℝ) lam hnR hlam).1
  have he : 9/(4*Real.sqrt (n:ℝ))=(9/4)*(1/Real.sqrt (n:ℝ)) := by ring
  rw [he] at hl
  let s : ℝ := 1/Real.sqrt (n:ℝ)
  have hg : 0<lam-(1+2*s) := by dsimp [s]; linarith
  refine ⟨lam-(1+2*s),hg,fun abc => ?_⟩
  have hpq := hPQ.1 abc.1 abc.2.1
  have hpr := hRP.2 abc.2.2 abc.1
  have hqr := hQR.1 abc.2.1 abc.2.2
  have hsqs : s^2=(n:ℝ)⁻¹ := by simpa only [s, one_div] using hsq
  have h := MUMNormBounds.triple_order_bound
    (P.proj abc.1) (Q.proj abc.2.1) (R.proj abc.2.2)
    (P.isProj _) (Q.isProj _) (R.isProj _) s hs
    (by simpa only [hsqs] using hpq) (by simpa only [hsqs] using hpr)
    (by simpa only [hsqs] using hqr)
  apply sub_nonneg.mp
  convert sub_nonneg.mpr h using 1 <;> (try dsimp [tripleSum]) <;> module

theorem cycleDefect_trace_eq_zero_of_selected_le (P Q R T : PVM n D)
    (hn : 2≤n) (hD : 0<D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (hselected : ∀ a b c d, ‖selectedSum P Q R T a b c d‖≤lam) :
    matTrace (cycleDefect P Q R)=0 := by
  have hnpos : 0<n := by omega
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have ht := cycleDefect_trace_nonneg P Q R hnpos hPQ hQR hRP
  by_contra hne
  have htpos : 0<matTrace (cycleDefect P Q R) := by positivity
  obtain ⟨g,hg,hgap⟩ := triple_resolvent_gap P Q R hn hPQ hQR hRP lam hlam
  have hres := fun abc => posDef_of_scalar_lower hg (hgap abc)
  obtain ⟨hk,hkb⟩ := cycleKappa_bounds hn lam hlam
  have hden : 0<1-6*cycleKappa n lam := by linarith
  have hfrac : 12*cycleKappa n lam/(1-6*cycleKappa n lam)<1 :=
    (div_lt_one hden).mpr (by linarith)
  have ha : 0<cycleKappa n lam*(1-12*cycleKappa n lam/(1-6*cycleKappa n lam)) :=
    mul_pos hk (sub_pos.mpr hfrac)
  have hdef := harmonic_trace_deficit P Q R hn hPQ hQR hRP lam hlam hres
  have hstrict : matTrace (tripleHarmonicMean P Q R lam)<(D:ℝ) := by
    have hp := mul_pos ha htpos
    linarith
  obtain ⟨⟨a,b,c⟩,d,hgt⟩ := selected_gt_of_harmonic_trace_lt hnpos hD
    (tripleSum P Q R) T lam g hg (tripleSum_nonneg P Q R) hgap hstrict
  exact (not_lt_of_ge (hselected a b c d)) hgt

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

theorem trace_cycleDefect_three_defectSquares (hn : 0<n)
    (P Q R : PVM n D) (hPQ : Unbiased P Q) (hQR : Unbiased Q R) :
    matTrace (cycleDefect P Q R)=3*matTrace (defectSquares P Q R) := by
  have h1 := matTrace_centeredCycle_cyclic P Q R
  have h2 := matTrace_centeredCycle_cyclic Q R P
  have h3 := trace_defectSquares_centeredCycle hn P Q R hPQ hQR
  have hadd : matTrace (cycleDefect P Q R)=
      matTrace (centeredCycle P Q R+star (centeredCycle P Q R))+
      matTrace (centeredCycle Q R P+star (centeredCycle Q R P))+
      matTrace (centeredCycle R P Q+star (centeredCycle R P Q)) := by
    simp only [cycleDefect, matTrace, Matrix.trace_add, Complex.add_re]
    ring
  rw [hadd]
  linarith

theorem equality_forces_triple_defects (P Q R T : PVM n D)
    (hn : 2≤n) (hD : 0<D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (hselected : ∀ a b c d, ‖selectedSum P Q R T a b c d‖≤lam) :
    ∀ a b c, defect P Q R a b c=0 := by
  have h := cycleDefect_trace_eq_zero_of_selected_le P Q R T hn hD hPQ hQR hRP lam hlam hselected
  rw [trace_cycleDefect_three_defectSquares (by omega) P Q R hPQ hQR] at h
  exact defect_eq_zero_of_trace_defectSquares P Q R (by linarith)

/-- Attaining the quartic bound forces all three anchored triple-unbiasedness equations. -/
theorem equality_forces_threefold_unbiased (P Q R T : PVM n D)
    (hn : 2≤n) (hD : 0<D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (hselected : ∀ a b c d, ‖selectedSum P Q R T a b c d‖≤lam) :
    (∀ a b c, P.proj a*(Q.proj b*R.proj c+R.proj c*Q.proj b)*P.proj a=
      (2/(n:ℝ)^2) • P.proj a) ∧
    (∀ b c a, Q.proj b*(R.proj c*P.proj a+P.proj a*R.proj c)*Q.proj b=
      (2/(n:ℝ)^2) • Q.proj b) ∧
    (∀ c a b, R.proj c*(P.proj a*Q.proj b+Q.proj b*P.proj a)*R.proj c=
      (2/(n:ℝ)^2) • R.proj c) := by
  have hp := equality_forces_triple_defects P Q R T hn hD hPQ hQR hRP lam hlam hselected
  have hq := equality_forces_triple_defects Q R P T hn hD hQR hRP hPQ lam hlam
    (fun b c a d => by simpa only [selectedSum, add_assoc, add_left_comm, add_comm] using hselected a b c d)
  have hr := equality_forces_triple_defects R P Q T hn hD hRP hPQ hQR lam hlam
    (fun c a b d => by simpa only [selectedSum, add_assoc, add_left_comm, add_comm] using hselected a b c d)
  exact ⟨fun a b c => sub_eq_zero.mp (hp a b c),
    fun b c a => sub_eq_zero.mp (hq b c a), fun c a b => sub_eq_zero.mp (hr c a b)⟩

/-- Any nonzero triple defect forces a strict improvement over the quartic bound. -/
theorem nonzero_defect_forces_strict_selected_sum (P Q R T : PVM n D)
    (hn : 2≤n) (hD : 0<D)
    (hPQ : Unbiased P Q) (hQR : Unbiased Q R) (hRP : Unbiased R P)
    (lam : ℝ) (hlam : LargestRoot n lam)
    (a b c : Fin n) (hdef : defect P Q R a b c ≠ 0) :
    ∃ a b c d : Fin n, lam < ‖selectedSum P Q R T a b c d‖ := by
  by_contra! hselected
  exact hdef (equality_forces_triple_defects P Q R T hn hD hPQ hQR hRP lam hlam hselected a b c)

end MUMSpectral


end


noncomputable section
open scoped BigOperators
namespace ProductBasisExtremum
abbrev BasisQuadruple := Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ

def IsOrthonormalProductQuadruple (B : BasisQuadruple) : Prop :=
  (∀ a i j, productBasisInner B a a i j = if i=j then 1 else 0) ∧
  (∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ), ∀ x y, B a i x y=u x*v y)

def pairEnergy (B : BasisQuadruple) (a b : Fin 4) : ℝ :=
  ∑ i, ∑ j, (Complex.normSq (productBasisInner B a b i j)-(1:ℝ)/6)^2

def squaredBengtssonDistance (B : BasisQuadruple) (a b : Fin 4) : ℝ :=
  1-pairEnergy B a b/5

theorem universal_error_lower_bound (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) : (2:ℝ)/3 ≤ productBasisEnergy B :=
  four_product_energy_lower_bound B hB.1 hB.2

theorem explicit_optimal_quadruple :
    ∃ B : BasisQuadruple, IsOrthonormalProductQuadruple B ∧
      productBasisEnergy B=(2:ℝ)/3 ∧
      (∀ a b, a<b → pairEnergy B a b=1/9) ∧
      (∀ a b, a<b → ∀ i j,
        |Complex.normSq (productBasisInner B a b i j)-(1:ℝ)/6|=1/18) ∧
      (∀ a b, a<b → squaredBengtssonDistance B a b=44/45) := by
  refine ⟨TetrahedralProductBases.rawBasis, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨TetrahedralProductBases.raw_orthonormal,TetrahedralProductBases.raw_product⟩
  · exact TetrahedralProductBases.raw_energy
  · exact TetrahedralProductBases.raw_pair_energy
  · exact TetrahedralProductBases.raw_entry_absolute_error
  · exact TetrahedralProductBases.raw_pair_distance

theorem exact_error_minimum :
    IsLeast {e : ℝ | ∃ B : BasisQuadruple,
      IsOrthonormalProductQuadruple B ∧ productBasisEnergy B=e} ((2:ℝ)/3) := by
  constructor
  · obtain ⟨B,hB,hE,_⟩ := explicit_optimal_quadruple
    exact ⟨B,hB,hE⟩
  · rintro e ⟨B,hB,rfl⟩
    exact universal_error_lower_bound B hB

theorem maximum_pair_error_lower_bound (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) :
    ∃ a b : Fin 4, a<b ∧ (1:ℝ)/9 ≤ pairEnergy B a b :=
  ProductMinimax.pair_lower_of_total (pairEnergy B) (universal_error_lower_bound B hB)

theorem maximum_entry_error_lower_bound (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) :
    ∃ a b : Fin 4, ∃ i j : Fin 6, a<b ∧
      (1:ℝ)/18 ≤ |Complex.normSq (productBasisInner B a b i j)-(1:ℝ)/6| :=
  ProductMinimax.entry_lower_of_total
    (fun a b i j => Complex.normSq (productBasisInner B a b i j)-(1:ℝ)/6)
    (universal_error_lower_bound B hB)

theorem mean_squared_distance_upper_bound (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) :
    (∑ a, ∑ b, if a<b then squaredBengtssonDistance B a b else 0)/6 ≤ (44:ℝ)/45 :=
  ProductMinimax.mean_distance_upper_of_total (pairEnergy B) (universal_error_lower_bound B hB)

theorem worst_pair_squared_distance_upper_bound (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) :
    ∃ a b : Fin 4, a<b ∧ squaredBengtssonDistance B a b ≤ (44:ℝ)/45 :=
  ProductMinimax.worst_pair_distance_upper_of_total (pairEnergy B) (universal_error_lower_bound B hB)

theorem no_four_mutually_unbiased_product_bases (B : BasisQuadruple)
    (hB : IsOrthonormalProductQuadruple B) :
    ¬ (∀ a b : Fin 4, a<b → ∀ i j : Fin 6,
      Complex.normSq (productBasisInner B a b i j)=(1:ℝ)/6) := by
  intro h
  obtain ⟨a,b,i,j,hab,he⟩ := maximum_entry_error_lower_bound B hB
  rw [h a b hab i j] at he
  norm_num at he
end ProductBasisExtremum
end

noncomputable section
open scoped BigOperators ComplexConjugate
namespace FourBasisScalar
theorem four_pair_zero_impurity (u : Fin 4 → ℝ) (z e : Fin 4 → Fin 4 → ℝ)
    (hu : ∀ a, 0 ≤ u a)
    (hz0 : ∀ a b, a<b → 0 ≤ z a b) (hz1 : ∀ a b, a<b → z a b ≤ 1)
    (hlow : ∀ a b, a<b → z a b-u a*u b ≤ e a b)
    (hrat : ∀ a b, a<b → z a b ≤ (2-z a b)*e a b)
    (hframe : 2/3+(∑ a, u a)/2 ≤ ∑ a, ∑ b, if a<b then z a b else 0)
    (hopt : (∑ a, ∑ b, if a<b then e a b else 0) = (2:ℝ)/3) :
    (∀ a, u a=0) ∧ (∑ a, ∑ b, if a<b then z a b else 0) = (2:ℝ)/3 := by
  let U := ∑ a, u a
  let Z := ∑ i, pairValues z i
  let E := ∑ i, pairValues e i
  have hU : 0 ≤ U := Finset.sum_nonneg fun a _ => hu a
  have hF : 2/3+U/2 ≤ Z := by simpa only [Z,U,pair_sum] using hframe
  have hE : E=(2:ℝ)/3 := by simpa only [E,pair_sum] using hopt
  have hlowSum : Z-(∑ i, pairValues (fun a b => u a*u b) i) ≤ E := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => hlow _ _ (pairIndex_lt i)
  have hprod := pair_product_bound u
  change 8*_ ≤ 3*U^2 at hprod
  have hR : 6*Z ≤ (12-Z)*E := six_rational_aggregate (pairValues z) (pairValues e)
    (fun i => hz0 _ _ (pairIndex_lt i)) (fun i => hz1 _ _ (pairIndex_lt i))
    (fun i => hrat _ _ (pairIndex_lt i))
  have hupp : U ≤ 16/15 := by rw [hE] at hR; linarith
  have hm := mul_nonneg hU (sub_nonneg.mpr hupp)
  have hU0 : U=0 := by nlinarith
  have hzero (a : Fin 4) : u a=0 := by
    have hh : u a ≤ U := Finset.single_le_sum (fun i _ => hu i) (Finset.mem_univ a)
    linarith [hu a]
  have hpair : (∑ i, pairValues (fun a b => u a*u b) i)=0 := by
    simp [pairValues,hzero]
  rw [hpair] at hlowSum
  constructor
  · exact hzero
  · change (∑ a, ∑ b, if a<b then z a b else 0)=(2:ℝ)/3
    rw [← pair_sum]
    change Z=(2:ℝ)/3
    linarith
end FourBasisScalar


namespace ProductPhysicalTransport
open scoped BigOperators

theorem upper_pair_le_sum (z : Fin 4 → Fin 4 → ℝ)
    (hn : ∀ a b, a<b → 0 ≤ z a b) (a b : Fin 4) (hab : a<b) :
    z a b ≤ ∑ i, ∑ j, if i<j then z i j else 0 := by
  have hpos (i j : Fin 4) : 0 ≤ if i<j then z i j else 0 := by
    split_ifs with h
    · exact hn i j h
    · exact le_rfl
  calc
    _ ≤ ∑ j, if a<j then z a j else 0 := by
      have hh := Finset.single_le_sum (fun j _ => hpos a j) (Finset.mem_univ b)
      simpa only [if_pos hab] using hh
    _ ≤ _ := Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => hpos i j) (Finset.mem_univ a)

theorem four_optimum_impurity_zero
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3) :
    (∀ a, impurity (P a)=0) ∧
      (∑ a, ∑ b, if a<b then frameCross (P a) (P b) else 0)=(2:ℝ)/3 := by
  exact FourBasisScalar.four_pair_zero_impurity (fun a => impurity (P a))
    (fun a b => frameCross (P a) (P b)) (fun a b => pairError (P a) (P b))
    (fun a => impurity_nonneg (P a))
    (fun a b _ => (frameCross_bounds (P a) (P b)).1)
    (fun a b _ => (frameCross_bounds (P a) (P b)).2)
    (fun a b _ => actual_pair_low_bound (P a) (P b))
    (fun a b _ => actual_pair_rational_bound (P a) (P b))
    (four_physical_frame_bound P) hopt

theorem four_optimum_pair_rigidity
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a<b) :
    pairError (P a) (P b)=frameCross (P a) (P b) ∧ frameCross (P a) (P b)<1 := by
  obtain ⟨hu,hz⟩ := four_optimum_impurity_zero P hopt
  have hg (i j : Fin 4) (_hij : i<j) :
      0 ≤ pairError (P i) (P j)-frameCross (P i) (P j) := by
    have hh := actual_pair_low_bound (P i) (P j)
    rw [hu i,zero_mul,sub_zero] at hh
    linarith
  have hsum : (∑ i, ∑ j, if i<j then
      pairError (P i) (P j)-frameCross (P i) (P j) else 0)=0 := by
    have heq : (∑ i, ∑ j, if i<j then
        pairError (P i) (P j)-frameCross (P i) (P j) else 0)=
      (∑ i, ∑ j, if i<j then pairError (P i) (P j) else 0)-
      (∑ i, ∑ j, if i<j then frameCross (P i) (P j) else 0) := by
      simp only [←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs <;> ring
    rw [heq,hopt,hz,sub_self]
  have hgap := upper_pair_le_sum (fun i j =>
    pairError (P i) (P j)-frameCross (P i) (P j)) hg a b hab
  rw [hsum] at hgap
  have hcross := upper_pair_le_sum (fun i j => frameCross (P i) (P j))
    (fun i j _ => (frameCross_bounds (P i) (P j)).1) a b hab
  rw [hz] at hcross
  constructor
  · linarith [hg a b hab]
  · linarith

theorem four_optimum_axes_coincide
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a : Fin 4) (i j : Fin 6) : axisVector (P a) i=axisVector (P a) j := by
  exact zero_impurity_axes_coincide (P a) ((four_optimum_impurity_zero P hopt).1 a) i j

end ProductPhysicalTransport
open scoped BigOperators

namespace ProductTetrahedral

theorem trace_norm_rigidity_three (S : Fin 3 → Fin 3 → ℝ)
    (htrace : (∑ x, S x x)=4)
    (hnorm : (∑ x, ∑ y, (S x y)^2)=16/3) :
    ∀ x y, S x y=if x=y then 4/3 else 0 := by
  have he : (∑ x, ∑ y, (S x y-(if x=y then 4/3 else 0))^2)=
      (∑ x, ∑ y, (S x y)^2)-(8/3:ℝ)*(∑ x, S x x)+16/3 := by
    simp only [Fin.sum_univ_three]
    norm_num [Fin.ext_iff]
    ring
  have hz : (∑ x, ∑ y, (S x y-(if x=y then 4/3 else 0))^2)=0 := by
    rw [he,htrace,hnorm]
    norm_num
  intro x y
  have hx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
    Finset.sum_nonneg fun y _ => sq_nonneg (S x y-(if x=y then 4/3 else 0)))).mp hz
    x (Finset.mem_univ x)
  have hxy := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
    sq_nonneg (S x y-(if x=y then 4/3 else 0)))).mp hx y (Finset.mem_univ y)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hxy)

theorem tight_four_vectors_equiangular (b : Fin 4 → Fin 3 → ℝ)
    (hunit : ∀ a, (∑ t, (b a t)^2)=1)
    (htight : ∀ x y, (∑ a, b a x*b a y)=if x=y then 4/3 else 0)
    (i j : Fin 4) (hij : i≠j) : (∑ t, b i t*b j t)^2=(1:ℝ)/9 := by
  let B : Matrix (Fin 4) (Fin 3) ℝ := b
  let G : Matrix (Fin 4) (Fin 4) ℝ := B*B.transpose
  have hBtB : B.transpose*B=(4/3:ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext x y
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.smul_apply,
      Matrix.one_apply,smul_eq_mul,mul_ite,mul_one,mul_zero] using htight x y
  have hG : G*G=(4/3:ℝ) • G := by
    dsimp [G]
    calc
      _ = B*(B.transpose*B)*B.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBtB,Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one]
  have hGdiag (a : Fin 4) : G a a=1 := by
    simpa only [G,Matrix.mul_apply,Matrix.transpose_apply,←sq] using hunit a
  have hGsym (a c : Fin 4) : G a c=G c a := by
    change (∑ t, b a t*b c t)=(∑ t, b c t*b a t)
    simp only [mul_comm]
  let K : Matrix (Fin 4) (Fin 4) ℝ := 1-(3/4:ℝ) • G
  have hK : K*K=K := by
    dsimp [K]
    simp only [sub_mul,mul_sub,one_mul,mul_one,smul_mul_assoc,mul_smul_comm,
      smul_smul,hG]
    module
  have hKdiag (a : Fin 4) : K a a=1/4 := by
    simp [K,Matrix.sub_apply,Matrix.smul_apply,hGdiag]
    norm_num
  have hKsym (a c : Fin 4) : K a c=K c a := by
    simp only [K,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]
    rw [hGsym a c]
    simp only [eq_comm]
  have hKinner (a c : Fin 4) : (∑ k, K a k*K c k)=K a c := by
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M a c) hK
    change (∑ k, K a k*K k c)=K a c at hh
    simpa only [hKsym _ c] using hh
  have hGbound (a c : Fin 4) (hac : a≠c) : (G a c)^2≤1/9 := by
    have hh := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (K a) (K c)
    have hKn (t : Fin 4) : (∑ k, (K t k)^2)=1/4 := by
      simpa only [sq,hKdiag] using hKinner t t
    rw [hKinner,hKn,hKn] at hh
    have he : K a c= -(3/4:ℝ)*G a c := by
      simp [K,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply,hac]
    rw [he] at hh
    nlinarith
  have hGn : (∑ k, (G i k)^2)=4/3 := by
    have hh := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i i) hG
    change (∑ k, G i k*G k i)=(4/3:ℝ)*G i i at hh
    simpa only [hGsym _ i,←sq,hGdiag,mul_one] using hh
  have hb (k : Fin 4) : (G i k)^2 ≤ if i=k then 1 else 1/9 := by
    by_cases h : i=k
    · subst k; simp [hGdiag]
    · simpa only [if_neg h] using hGbound i k h
  have hs : (∑ k : Fin 4, if i=k then (1:ℝ) else 1/9)=4/3 := by
    have he (k : Fin 4) : (if i=k then (1:ℝ) else 1/9)=
        1/9+(if i=k then 8/9 else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    simp [Finset.sum_add_distrib]
    norm_num
  have heq : (G i j)^2=1/9 := by
    by_contra hn
    have hlt : (G i j)^2<1/9 := lt_of_le_of_ne (hGbound i j hij) hn
    have hh := Finset.sum_lt_sum (fun k _ => hb k)
      ⟨j,Finset.mem_univ j,by simpa only [if_neg hij] using hlt⟩
    rw [hGn,hs] at hh
    exact (lt_irrefl _ hh)
  exact heq

end ProductTetrahedral
namespace ProductPhysicalTransport
open ProductGeometry ProductCovariance ProductTetrahedral

theorem zero_impurity_mean_axis (P : NormalizedProductBasis) (h : impurity P=0)
    (k : Fin 3 × Fin 3) : frameMean P k=axisVector P 0 k := by
  unfold frameMean
  calc
    _ = ∑ _i : Fin 6, (1/6:ℝ)*axisVector P 0 k := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [congrFun (zero_impurity_axes_coincide P h i 0) k]
    _ = _ := by norm_num; ring

theorem four_optimum_bloch_tight
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3) :
    ∀ x y, (∑ a, (P a).b 0 x*(P a).b 0 y)=if x=y then 4/3 else 0 := by
  obtain ⟨hu,hz⟩ := four_optimum_impurity_zero P hopt
  let S : Fin 3 → Fin 3 → ℝ := fun x y => ∑ a, frameMean (P a) (x,y)
  have htrace : (∑ x, S x x)=4 := by
    unfold S
    rw [Finset.sum_comm]
    simp only [frameMean_trace,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one,Nat.cast_ofNat]
  have hfnorm (a : Fin 4) : (∑ x, ∑ y, (frameMean (P a) (x,y))^2)=1 := by
    have hh := hu a
    unfold impurity at hh
    rw [Fintype.sum_prod_type] at hh
    linarith
  have hpair : (∑ a, ∑ b, if a<b then
      ∑ x, ∑ y, frameMean (P a) (x,y)*frameMean (P b) (x,y) else 0)=(2:ℝ)/3 := by
    simpa only [frameCross,Fintype.sum_prod_type] using hz
  have hnorm : (∑ x, ∑ y, (S x y)^2)=16/3 := by
    unfold S
    rw [four_frame_expansion,hpair]
    simp only [hfnorm,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    norm_num
  have hs := trace_norm_rigidity_three S htrace hnorm
  have hmean (a : Fin 4) (k : Fin 3 × Fin 3) :
      frameMean (P a) k=axisVector (P a) 0 k := zero_impurity_mean_axis (P a) (hu a) k
  intro x y
  simpa only [S,hmean,axisVector] using hs x y

theorem four_optimum_tetrahedral
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) :
    (∑ t, (P a).b 0 t*(P b).b 0 t)^2=(1:ℝ)/9 := by
  exact tight_four_vectors_equiangular (fun a => (P a).b 0)
    (fun a => bloch_unit (P a) 0) (four_optimum_bloch_tight P hopt) a b hab

theorem four_optimum_frameCross
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) : frameCross (P a) (P b)=(1:ℝ)/9 := by
  have hu := (four_optimum_impurity_zero P hopt).1
  unfold frameCross
  simp_rw [zero_impurity_mean_axis (P a) (hu a),zero_impurity_mean_axis (P b) (hu b)]
  simpa only [axisVector,outer_inner] using four_optimum_tetrahedral P hopt a b hab

end ProductPhysicalTransport
namespace ProductPairEquality
open scoped BigOperators ComplexConjugate
open ProductPhysicalTransport ProductGeometry ProductCovariance

noncomputable def qubitWeight (P Q : NormalizedProductBasis) (i j : Fin 6) : ℝ :=
  (1+(∑ t, P.b i t*Q.b j t))/2

theorem qubitWeight_eq_overlap (P Q : NormalizedProductBasis) (i j : Fin 6) :
    qubitWeight P Q i j=Complex.normSq (∑ x, star (P.u i x)*Q.u j x) := by
  have h := bloch_overlap (P.u i) (Q.u j)
  rw [P.hu,Q.hu] at h
  change 2*Complex.normSq (∑ x, star (P.u i x)*Q.u j x)=
    1*1+∑ t, P.b i t*Q.b j t at h
  unfold qubitWeight
  linarith

theorem qubitWeight_row_sum (P Q : NormalizedProductBasis) (i : Fin 6) :
    (∑ j, qubitWeight P Q i j)=3 := by
  have hc (y : Fin 3) := tensor_compression Q.u Q.v (P.u i) (P.hu i) Q.hres y y
  have hv (j : Fin 6) : (∑ y, Q.v j y*star (Q.v j y))=1 := by
    have h := congrArg (fun t : ℝ => (t:ℂ)) (Q.hv j)
    simpa only [Complex.ofReal_sum, ← Complex.mul_conj, starRingEnd_apply,
      Complex.ofReal_one] using h
  have h := Finset.sum_congr rfl (fun y (_ : y∈Finset.univ) => hc y)
  rw [Finset.sum_comm] at h
  simp only [mul_assoc, ← Finset.mul_sum, hv, mul_one, if_pos rfl,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  simp_rw [qubitWeight_eq_overlap]
  exact_mod_cast h

theorem zero_impurity_mean (P : NormalizedProductBasis) (hP : impurity P=0)
    (i : Fin 6) (k : Fin 3 × Fin 3) : frameMean P k=axisVector P i k := by
  unfold frameMean
  simp_rw [zero_impurity_axes_coincide P hP _ i]
  norm_num
  ring

theorem zero_impurity_cross (P Q : NormalizedProductBasis)
    (hP : impurity P=0) (hQ : impurity Q=0) (i j : Fin 6) :
    (∑ t, P.b i t*Q.b j t)^2=frameCross P Q := by
  unfold frameCross
  simp_rw [zero_impurity_mean P hP i, zero_impurity_mean Q hQ j]
  exact (outer_inner (P.b i) (Q.b j)).symm

theorem qubitWeight_positive (P Q : NormalizedProductBasis)
    (hP : impurity P=0) (hQ : impurity Q=0) (hlt : frameCross P Q<1)
    (i j : Fin 6) : 0<qubitWeight P Q i j := by
  have hs := zero_impurity_cross P Q hP hQ i j
  have hd : -1<(∑ t, P.b i t*Q.b j t) := by
    nlinarith [sq_nonneg ((∑ t, P.b i t*Q.b j t)+1)]
  unfold qubitWeight
  linarith

theorem qubitWeight_square (P Q : NormalizedProductBasis)
    (hP : impurity P=0) (hQ : impurity Q=0) (i j : Fin 6) :
    (qubitWeight P Q i j)^2=qubitWeight P Q i j+(frameCross P Q-1)/4 := by
  have h := zero_impurity_cross P Q hP hQ i j
  unfold qubitWeight
  nlinarith

theorem qubitWeight_product (P Q : NormalizedProductBasis) (i j : Fin 6) :
    qubitWeight P Q i j*qutritTransition P Q i j=productTransition P Q i j :=
  (product_transition_bloch P Q i j).symm

theorem weighted_qutrit_centered_identity (P Q : NormalizedProductBasis)
    (hP : impurity P=0) (hQ : impurity Q=0) :
    (∑ i, ∑ j, (qubitWeight P Q i j)^2*(qutritTransition P Q i j-1/3)^2)=
      pairError P Q-frameCross P Q := by
  have hw : (∑ i, ∑ j, (qubitWeight P Q i j)^2)=9*(1+frameCross P Q) := by
    simp_rw [qubitWeight_square P Q hP hQ]
    simp only [Finset.sum_add_distrib, qubitWeight_row_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hm : (∑ i, ∑ j, (qubitWeight P Q i j)^2*qutritTransition P Q i j)=
      3*(1+frameCross P Q) := by
    simp_rw [qubitWeight_square P Q hP hQ, add_mul, qubitWeight_product]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      productTransition_row_sum, qutrit_transition_row,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have he (q m : ℝ) : q^2*(m-1/3)^2=(q*m)^2-(2/3)*(q^2*m)+(1/9)*q^2 := by ring
  simp_rw [he, qubitWeight_product]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hw,hm]
  unfold pairError
  ring

theorem saturated_pair_qutrit_flat (P Q : NormalizedProductBasis)
    (hP : impurity P=0) (hQ : impurity Q=0)
    (he : pairError P Q=frameCross P Q) (hlt : frameCross P Q<1)
    (i j : Fin 6) : qutritTransition P Q i j=1/3 := by
  have hs := weighted_qutrit_centered_identity P Q hP hQ
  rw [he,sub_self] at hs
  have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hs i
      (Finset.mem_univ i)
  have hij := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _))).mp hi j (Finset.mem_univ j)
  have hpos := qubitWeight_positive P Q hP hQ hlt i j
  have hz := (mul_eq_zero.mp hij).resolve_left (ne_of_gt (sq_pos_of_pos hpos))
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hz)

end ProductPairEquality
namespace ProductPhysicalTransport
open scoped BigOperators

theorem four_optimum_qutrit_flat
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 6) :
    qutritTransition (P a) (P b) i j=1/3 := by
  have hu := (four_optimum_impurity_zero P hopt).1
  rcases lt_or_gt_of_ne hab with hl | hl
  · obtain ⟨he,hlt⟩ := four_optimum_pair_rigidity P hopt a b hl
    exact ProductPairEquality.saturated_pair_qutrit_flat (P a) (P b)
      (hu a) (hu b) he hlt i j
  · rw [qutrit_transition_symm]
    obtain ⟨he,hlt⟩ := four_optimum_pair_rigidity P hopt b a hl
    exact ProductPairEquality.saturated_pair_qutrit_flat (P b) (P a)
      (hu b) (hu a) he hlt j i

theorem raw_optimum_normalized_rigidity
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j=if i=j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y=u x*v y)
    (hopt : productBasisEnergy B=(2:ℝ)/3) :
    ∃ P : Fin 4 → NormalizedProductBasis,
      (∀ a i x y, B a i x y=(P a).u i x*(P a).v i y) ∧
      (∀ a i j, axisVector (P a) i=axisVector (P a) j) ∧
      (∀ a b, a≠b → ∀ i j, qutritTransition (P a) (P b) i j=1/3) := by
  classical
  have ho : ∀ a i j, productBasisInner B a a i j=
      @ite ℂ (i=j) (Classical.propDecidable (i=j)) 1 0 := by
    intro a i j
    by_cases h : i=j
    · simpa only [if_pos h] using horth a i j
    · simpa only [if_neg h] using horth a i j
  obtain ⟨P,hP⟩ := normalized_bases_from_raw B ho hproduct
  have ht (a b : Fin 4) (i j : Fin 6) : productTransition (P a) (P b) i j=
      Complex.normSq (productBasisInner B a b i j) := by
    unfold productTransition productBasisInner
    simp_rw [hP]
  have he : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3 := by
    simpa only [pairError_eq_centered_squares,ht,productBasisEnergy] using hopt
  exact ⟨P,hP,four_optimum_axes_coincide P he,four_optimum_qutrit_flat P he⟩

end ProductPhysicalTransport
namespace ProductBranchExtraction
open scoped BigOperators ComplexConjugate
open ProductPhysicalTransport ProductGeometry ProductCoarseGraining

 theorem axis_dichotomy (P : NormalizedProductBasis) (hP : impurity P=0)
    (i j : Fin 6) : P.b j=P.b i ∨ P.b j= -P.b i := by
  have haxis : qubitAxis (P.u j)=qubitAxis (P.u i) := by
    funext x y
    exact congrFun (zero_impurity_axes_coincide P hP j i) (x,y)
  rcases (same_axis_iff_extreme_overlap (P.u j) (P.u i) (P.hu j) (P.hu i)).mp haxis
    with hzero | hone
  · exact Or.inr ((opposite_bloch_iff_overlap_zero _ _ (P.hu j) (P.hu i)).mpr hzero)
  · exact Or.inl ((same_bloch_iff_overlap_one _ _ (P.hu j) (P.hu i)).mpr hone)

 theorem bloch_ne_neg (P : NormalizedProductBasis) (i : Fin 6) : P.b i≠ -P.b i := by
  intro h
  have hz (k : Fin 3) : P.b i k=0 := by
    have hk := congrFun h k
    simp only [Pi.neg_apply] at hk
    linarith
  have hn := bloch_unit P i
  simp only [hz,zero_pow (by omega : 2≠0), Finset.sum_const_zero] at hn
  norm_num at hn

 theorem same_axis_fiber_card (P : NormalizedProductBasis) (hP : impurity P=0)
    (i : Fin 6) : (fiber P.b i).card=3 := by
  classical
  have hd : Disjoint (fiber P.b i) (oppositeFiber P.b i) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have hj' : P.b j=P.b i := by simpa only [fiber,Finset.mem_filter,Finset.mem_univ,true_and] using hj
    have hk' : P.b j= -P.b i := by simpa only [oppositeFiber,Finset.mem_filter,Finset.mem_univ,true_and] using hk
    exact bloch_ne_neg P i (hj'.symm.trans hk')
  have hu : fiber P.b i ∪ oppositeFiber P.b i=Finset.univ := by
    ext j
    simp only [Finset.mem_union, fiber, oppositeFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, iff_true]
    exact axis_dichotomy P hP i j
  have hc := Finset.card_union_of_disjoint hd
  rw [hu, Finset.card_univ, Fintype.card_fin, P.balanced i] at hc
  omega

noncomputable def positiveBranch (P : NormalizedProductBasis) (hP : impurity P=0) :
    Fin 3 ↪ Fin 6 :=
  let e := (Finset.equivFinOfCardEq (same_axis_fiber_card P hP 0)).symm
  ⟨fun j => (e j).val, fun i j hij => e.injective (Subtype.ext hij)⟩

 theorem positiveBranch_bloch (P : NormalizedProductBasis) (hP : impurity P=0)
    (j : Fin 3) : P.b (positiveBranch P hP j)=P.b 0 := by
  have hs (x : ↥(fiber P.b 0)) : P.b x=P.b 0 := by
    simpa only [fiber,Finset.mem_filter,Finset.mem_univ,true_and] using x.property
  dsimp only [positiveBranch]
  exact hs _

 theorem positiveBranch_unit (P : NormalizedProductBasis) (hP : impurity P=0)
    (j : Fin 3) : (∑ k, Complex.normSq (P.v (positiveBranch P hP j) k))=1 :=
  P.hv _

 theorem positiveBranch_orthonormal (P : NormalizedProductBasis) (hP : impurity P=0)
    (i j : Fin 3) :
    (∑ k, star (P.v (positiveBranch P hP i) k)*P.v (positiveBranch P hP j) k)=
      if i=j then 1 else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    have h := congrArg (fun r : ℝ => (r:ℂ)) (P.hv (positiveBranch P hP i))
    simpa only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply, Complex.ofReal_one] using h
  · rw [if_neg hij]
    have hne : positiveBranch P hP i≠positiveBranch P hP j :=
      (positiveBranch P hP).injective.ne hij
    have hp := P.horth (positiveBranch P hP i) (positiveBranch P hP j)
    rw [if_neg hne, tensor_inner_factor] at hp
    have hb : P.b (positiveBranch P hP i)=P.b (positiveBranch P hP j) := by
      rw [positiveBranch_bloch,positiveBranch_bloch]
    have ho := (same_bloch_iff_overlap_one _ _
      (P.hu (positiveBranch P hP i)) (P.hu (positiveBranch P hP j))).mp hb
    apply (mul_eq_zero.mp hp).resolve_left
    intro hz
    rw [hz, map_zero] at ho
    norm_num at ho

end ProductBranchExtraction
namespace ProductBranchExtraction
open scoped BigOperators
open ProductPhysicalTransport

noncomputable def optimalQutritBranches
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3) :
    Fin 4 → Fin 3 → Fin 3 → ℂ :=
  fun a j => (P a).v (positiveBranch (P a) ((four_optimum_impurity_zero P hopt).1 a) j)

theorem optimalQutritBranches_orthonormal
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a : Fin 4) (i j : Fin 3) :
    (∑ k, star (optimalQutritBranches P hopt a i k)*optimalQutritBranches P hopt a j k)=
      if i=j then 1 else 0 :=
  positiveBranch_orthonormal (P a) ((four_optimum_impurity_zero P hopt).1 a) i j

theorem optimalQutritBranches_unbiased
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 3) :
    Complex.normSq (∑ k, star (optimalQutritBranches P hopt a i k)*
      optimalQutritBranches P hopt b j k)=1/3 :=
  four_optimum_qutrit_flat P hopt a b hab _ _

theorem original_qutrit_unbiased_other_branch
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i : Fin 6) (j : Fin 3) :
    Complex.normSq (∑ k, star (optimalQutritBranches P hopt b j k)*(P a).v i k)=1/3 :=
  four_optimum_qutrit_flat P hopt b a hab.symm _ i

end ProductBranchExtraction

open scoped BigOperators Matrix
namespace QutritProjectorAdapter
abbrev Vec := Fin 3 → ℂ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℂ
def inner (v w : Vec) : ℂ := ∑ x, star (v x)*w x
def projector (v : Vec) : Mat := fun x y => v x*star (v y)

theorem trace_projector (v : Vec) :
    Matrix.trace (projector v)=inner v v := by
  simp only [Matrix.trace,Matrix.diag,projector,inner]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem projector_mul (v w : Vec) (x y : Fin 3) :
    (projector v*projector w) x y=v x*inner v w*star (w y) := by
  simp only [Matrix.mul_apply,projector,inner,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem trace_mul (v w : Vec) :
    Matrix.trace (projector v*projector w)=(Complex.normSq (inner v w):ℂ) := by
  simp only [Matrix.trace,Matrix.diag,projector_mul]
  have hstar : star (inner v w)=∑ x, v x*star (w x) := by
    simp [inner,map_sum,star_mul,mul_comm]
  rw [Complex.normSq_eq_conj_mul_self]
  change _ = star (inner v w)*inner v w
  rw [hstar,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem projector_idempotent (v : Vec) (hv : inner v v=1) :
    projector v*projector v=projector v := by
  ext x y
  simp [projector_mul,hv,projector]

theorem projector_orthogonal (v w : Vec) (h : inner v w=0) :
    projector v*projector w=0 := by
  ext x y
  simp [projector_mul,h]

theorem onb_multiplication (V : Fin 3 → Vec)
    (hV : ∀ i j,inner (V i) (V j)=if i=j then 1 else 0) :
    ∀ i j, projector (V i)*projector (V j)=if i=j then projector (V i) else 0 := by
  intro i j
  by_cases h : i=j
  · subst j
    simp only [ite_true]
    exact projector_idempotent _ (by simpa using hV i i)
  · simp only [h,ite_false]
    exact projector_orthogonal _ _ (by simpa [h] using hV i j)

theorem onb_resolution (V : Fin 3 → Vec)
    (hV : ∀ i j,inner (V i) (V j)=if i=j then 1 else 0) :
    ∑ i,projector (V i)=1 := by
  let A : Mat := fun x i => V i x
  let B : Mat := fun i x => star (V i x)
  have hBA : B*A=1 := by
    ext i j
    exact hV i j
  have hAB := mul_eq_one_comm.mp hBA
  ext x y
  change (∑ i, V i x*star (V i y))=(1 : Mat) x y
  change (A*B) x y=(1 : Mat) x y
  exact congrFun (congrFun hAB x) y


theorem four_onb_trace_data (V : Fin 4 → Fin 3 → Vec)
    (hV : ∀ a i j,inner (V a i) (V a j)=if i=j then 1 else 0)
    (hMU : ∀ a b, a≠b → ∀ i j,Complex.normSq (inner (V a i) (V b j))=1/3) :
    (∀ a i,Matrix.trace (projector (V a i))=1) ∧
    (∀ a b i j,Matrix.trace (projector (V a i)*projector (V b j))=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ)) ∧
    (∀ a,∑ i,projector (V a i)=1) ∧
    (∀ a i j,projector (V a i)*projector (V a j)=
      if i=j then projector (V a i) else 0) := by
  refine ⟨?_,?_,fun a => onb_resolution (V a) (hV a),fun a => onb_multiplication (V a) (hV a)⟩
  · intro a i
    rw [trace_projector,hV]
    simp
  · intro a b i j
    rw [trace_mul]
    by_cases hab : a=b
    · subst b
      rw [hV]
      by_cases hij : i=j <;> simp [hij]
    · rw [hMU a b hab i j]
      simp [hab]
end QutritProjectorAdapter

namespace QutritMUBCompleteness
abbrev M := Matrix (Fin 3) (Fin 3) ℂ
abbrev Ix := Option (Fin 4 × Fin 2)

def frame (P : Fin 4 → Fin 3 → M) : Ix → M
  | none => 1
  | some (a,i) => P a i.castSucc-P a (Fin.last 2)

noncomputable def dual (P : Fin 4 → Fin 3 → M) : Ix → M
  | none => (1/3:ℂ) • 1
  | some (a,i) => P a i.castSucc-(1/3:ℂ) • 1

theorem frame_duality (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ)) :
    ∀ i j : Ix, Matrix.trace (dual P i*frame P j)=if i=j then 1 else 0 := by
  intro i j
  cases i with
  | none =>
    cases j with
    | none => norm_num [dual,frame,Matrix.trace_one]
    | some bj =>
      rcases bj with ⟨b,j⟩
      simp [dual,frame,mul_sub,Matrix.trace_sub,Matrix.trace_smul,ht]
  | some ai =>
    rcases ai with ⟨a,i⟩
    cases j with
    | none => norm_num [dual,frame,Matrix.trace_sub,Matrix.trace_smul,ht,Matrix.trace_one] <;> simp
    | some bj =>
      rcases bj with ⟨b,j⟩
      simp only [dual,frame,mul_sub,sub_mul,smul_mul_assoc,one_mul,Matrix.trace_sub,
        Matrix.trace_smul,ht,hg,smul_eq_mul]
      have hi : i.castSucc ≠ (2:Fin 3) := Fin.castSucc_ne_last i
      by_cases hab : a=b
      · subst b
        simp [hi,Fin.castSucc_inj]
      · simp [hab]

theorem frame_linearIndependent (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ)) :
    LinearIndependent ℂ (frame P) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro f hf i
  have h := congrArg (fun X => Matrix.trace (dual P i*X)) hf
  simp only [Finset.mul_sum,Matrix.trace_sum,mul_smul_comm,Matrix.trace_smul,
    smul_eq_mul,frame_duality P ht hg,mul_zero,Matrix.trace_zero] at h
  simpa using h

theorem frame_spans (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ)) :
    Submodule.span ℂ (Set.range (frame P))=⊤ := by
  apply (frame_linearIndependent P ht hg).span_eq_top_of_card_eq_finrank'
  norm_num [Ix,M,Module.finrank_matrix]

theorem determined_by_pairings (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ))
    (X Y : M) (htr : Matrix.trace X=Matrix.trace Y)
    (hp : ∀ a i, Matrix.trace (P a i*X)=Matrix.trace (P a i*Y)) : X=Y := by
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Z
  have hz : Z ∈ Submodule.span ℂ (Set.range (frame P)) := by
    rw [frame_spans P ht hg]
    trivial
  induction hz using Submodule.span_induction with
  | mem W hw =>
    obtain ⟨i,rfl⟩ := hw
    cases i with
    | none => simpa [frame] using htr
    | some ai =>
      rcases ai with ⟨a,i⟩
      simp [frame,sub_mul,Matrix.trace_sub,hp]
  | zero => simp
  | add W V _ _ hw hv => simpa [add_mul,Matrix.trace_add,hw,hv]
  | smul c W _ hw => simpa [smul_mul_assoc,Matrix.trace_smul,hw]

theorem diagonal_reconstruction (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ))
    (hs : ∀ a, ∑ j, P a j=1)
    (X : M) (a0 : Fin 4) (htr : Matrix.trace X=1)
    (hp : ∀ a, a≠a0 → ∀ i, Matrix.trace (P a i*X)=(1/3:ℂ)) :
    X=∑ j, Matrix.trace (P a0 j*X) • P a0 j := by
  classical
  have hc : ∑ j, Matrix.trace (P a0 j*X)=1 := by
    rw [← Matrix.trace_sum,← Finset.sum_mul,hs,one_mul,htr]
  apply determined_by_pairings P ht hg
  · simpa [Matrix.trace_sum,Matrix.trace_smul,ht,smul_eq_mul] using htr.trans hc.symm
  · intro a i
    simp only [Finset.mul_sum,Matrix.trace_sum,mul_smul_comm,Matrix.trace_smul,
      smul_eq_mul,hg]
    by_cases ha : a=a0
    · subst a
      simp
    · rw [hp a ha i]
      simp only [ha,ite_false]
      rw [← Finset.sum_mul,hc]
      norm_num

theorem unbiased_three_saturation (P : Fin 4 → Fin 3 → M)
    (ht : ∀ a i, Matrix.trace (P a i)=1)
    (hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ))
    (hs : ∀ a, ∑ j, P a j=1)
    (hmul : ∀ a i j, P a i*P a j=if i=j then P a i else 0)
    (X : M) (a0 : Fin 4) (htr : Matrix.trace X=1) (hX : X*X=X)
    (hp : ∀ a, a≠a0 → ∀ i, Matrix.trace (P a i*X)=(1/3:ℂ)) :
    ∃ j, Matrix.trace (P a0 j*X)=1 := by
  classical
  let c : Fin 3 → ℂ := fun j => Matrix.trace (P a0 j*X)
  have hd := diagonal_reconstruction P ht hg hs X a0 htr hp
  have hpx (j : Fin 3) : P a0 j*X=c j • P a0 j := by
    conv_lhs => rw [hd]
    simp [Finset.mul_sum,mul_smul_comm,hmul,c]
  have hi (j : Fin 3) : c j*c j=c j := by
    have hh := congrArg (fun Z => Matrix.trace (P a0 j*Z)) hX
    rw [← mul_assoc,hpx,smul_mul_assoc,hpx,Matrix.trace_smul,
      Matrix.trace_smul,ht] at hh
    simpa [c,smul_eq_mul] using hh
  have hc : ∑ j, c j=1 := by
    dsimp [c]
    rw [← Matrix.trace_sum,← Finset.sum_mul,hs,one_mul,htr]
  by_contra hn
  push_neg at hn
  have hz (j : Fin 3) : c j=0 := by
    have hprod : c j*(c j-1)=0 := by rw [mul_sub,hi,mul_one,sub_self]
    exact (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr (hn j))
  simp [hz] at hc

theorem unbiased_three_normSq_one
    (R : Fin 4 → Fin 3 → Fin 3 → ℂ)
    (horth : ∀ a i j, (∑ x, star (R a i x)*R a j x)=if i=j then 1 else 0)
    (hmub : ∀ a b, a≠b → ∀ i j,
      Complex.normSq (∑ x, star (R a i x)*R b j x)=(1/3:ℝ))
    (z : Fin 3 → ℂ) (hz : (∑ x, Complex.normSq (z x))=1)
    (a0 : Fin 4)
    (hunb : ∀ a, a≠a0 → ∀ i,
      Complex.normSq (∑ x, star (R a i x)*z x)=(1/3:ℝ)) :
    ∃ j, Complex.normSq (∑ x, star (R a0 j x)*z x)=1 := by
  classical
  let P : Fin 4 → Fin 3 → M := fun a j => QutritProjectorAdapter.projector (R a j)
  let X : M := QutritProjectorAdapter.projector z
  have ht : ∀ a i, Matrix.trace (P a i)=1 := by
    intro a i
    simpa [P,QutritProjectorAdapter.trace_projector,QutritProjectorAdapter.inner] using horth a i i
  have hg : ∀ a b i j, Matrix.trace (P a i*P b j)=
      if a=b then if i=j then 1 else 0 else (1/3:ℂ) := by
    intro a b i j
    rw [QutritProjectorAdapter.trace_mul]
    by_cases hab : a=b
    · subst b
      simp only [QutritProjectorAdapter.inner,horth,ite_true]
      split_ifs <;> norm_num
    · change (Complex.normSq (∑ x,star (R a i x)*R b j x):ℂ)=_
      rw [hmub a b hab i j]
      simp [hab]
  have hs : ∀ a, ∑ j, P a j=1 := by
    intro a
    exact QutritProjectorAdapter.onb_resolution (R a) (horth a)
  have hmul : ∀ a i j, P a i*P a j=if i=j then P a i else 0 := by
    intro a
    exact QutritProjectorAdapter.onb_multiplication (R a) (horth a)
  have hz' : QutritProjectorAdapter.inner z z=1 := by
    have hcast := congrArg (fun r : ℝ => (r:ℂ)) hz
    change Complex.ofRealHom (∑ x,Complex.normSq (z x))=1 at hcast
    rw [map_sum] at hcast
    simp only [Complex.ofRealHom_eq_coe,Complex.normSq_eq_conj_mul_self] at hcast
    exact hcast
  have htr : Matrix.trace X=1 := by
    exact (QutritProjectorAdapter.trace_projector z).trans hz'
  have hX : X*X=X := QutritProjectorAdapter.projector_idempotent z hz'
  have hp : ∀ a, a≠a0 → ∀ i, Matrix.trace (P a i*X)=(1/3:ℂ) := by
    intro a ha i
    rw [QutritProjectorAdapter.trace_mul]
    change (Complex.normSq (∑ x,star (R a i x)*z x):ℂ)=_
    rw [hunb a ha i]
    norm_num
  obtain ⟨j,hj⟩ := unbiased_three_saturation P ht hg hs hmul X a0 htr hX hp
  refine ⟨j,?_⟩
  simpa [P,X,QutritProjectorAdapter.trace_mul,QutritProjectorAdapter.inner] using
    congrArg Complex.re hj

end QutritMUBCompleteness
open scoped BigOperators ComplexConjugate

namespace ProductPhaseRecovery

theorem unit_overlap_phase {ι : Type*} [Fintype ι]
    (v w : ι → ℂ)
    (hv : (∑ k, Complex.normSq (v k))=1)
    (hw : (∑ k, Complex.normSq (w k))=1)
    (hip : Complex.normSq (∑ k, star (w k)*v k)=1) :
    ∃ c : ℂ, Complex.normSq c=1 ∧ ∀ k, v k=c*w k := by
  let c : ℂ := ∑ k, star (w k)*v k
  have hc : Complex.normSq c=1 := hip
  have hcross : (∑ k, v k*conj (c*w k))=conj c*c := by
    change (∑ k, v k*conj (c*w k))=conj c*(∑ k, star (w k)*v k)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [map_mul,starRingEnd_apply]
    ring
  have hreal : (∑ k, (v k*conj (c*w k)).re)=1 := by
    rw [←Complex.re_sum,hcross]
    have hn := congrArg Complex.re (Complex.normSq_eq_conj_mul_self (z:=c))
    simpa only [Complex.ofReal_re,hc] using hn.symm
  have hz : (∑ k, Complex.normSq (v k-c*w k))=0 := by
    simp_rw [Complex.normSq_sub,Complex.normSq_mul]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
      ←Finset.mul_sum,hv,hw,hc,hreal]
    norm_num
  refine ⟨c,hc,?_⟩
  intro k
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ =>
    Complex.normSq_nonneg (v k-c*w k))).mp hz k (Finset.mem_univ k)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp hk)

end ProductPhaseRecovery

namespace ProductPhaseRecovery

theorem orthonormal_phase_labels_injective {ι κ α : Type*}
    [Fintype α] [DecidableEq ι]
    (B : ι → α → ℂ) (T : κ → α → ℂ) (label : ι → κ) (c : ι → ℂ)
    (hB : ∀ i j, (∑ x, star (B i x)*B j x)=if i=j then 1 else 0)
    (hT : ∀ k, (∑ x, Complex.normSq (T k x))=1)
    (hc : ∀ i, Complex.normSq (c i)=1)
    (hf : ∀ i x, B i x=c i*T (label i) x) : Function.Injective label := by
  intro i j hij
  by_contra hne
  have hh := hB i j
  rw [if_neg hne] at hh
  have ht : (∑ x, star (T (label i) x)*T (label i) x)=1 := by
    have hn := congrArg (fun r : ℝ => (r:ℂ)) (hT (label i))
    simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,Complex.ofReal_one,
      starRingEnd_apply] using hn
  have he : (∑ x, star (B i x)*B j x)=star (c i)*c j := by
    simp only [hf,hij]
    calc
      (∑ x, star (c i*T (label j) x)*(c j*T (label j) x))=
          (star (c i)*c j)*(∑ x, star (T (label j) x)*T (label j) x) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [star_mul]
        ring
      _ = star (c i)*c j := by rw [←hij,ht,mul_one]
  rw [he] at hh
  have hn := congrArg Complex.normSq hh
  have hs (z : ℂ) : Complex.normSq (star z)=Complex.normSq z := Complex.normSq_conj z
  rw [Complex.normSq_mul,hs,hc,hc,Complex.normSq_zero] at hn
  norm_num at hn

theorem orthonormal_phase_labels_bijective {ι κ α : Type*}
    [Fintype ι] [Fintype κ] [Fintype α] [DecidableEq ι]
    (hcard : Fintype.card ι=Fintype.card κ)
    (B : ι → α → ℂ) (T : κ → α → ℂ) (label : ι → κ) (c : ι → ℂ)
    (hB : ∀ i j, (∑ x, star (B i x)*B j x)=if i=j then 1 else 0)
    (hT : ∀ k, (∑ x, Complex.normSq (T k x))=1)
    (hc : ∀ i, Complex.normSq (c i)=1)
    (hf : ∀ i x, B i x=c i*T (label i) x) : Function.Bijective label := by
  have hi := orthonormal_phase_labels_injective B T label c hB hT hc hf
  exact ⟨hi,(Fintype.bijective_iff_injective_and_card label).2 ⟨hi,hcard⟩ |>.2⟩

end ProductPhaseRecovery
/-- A direct tensor-product presentation, up to independent unit phases and
    permutation of the six vectors in each basis. The qubit lines are
    tetrahedral, and the four qutrit bases are mutually unbiased. -/
def HasDirectTetrahedralPresentation
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ) : Prop :=
  ∃ (U : Fin 4 → Fin 2 → Fin 2 → ℂ)
    (R : Fin 4 → Fin 3 → Fin 3 → ℂ)
    (sigma : Fin 4 → (Fin 6 ≃ Fin 2 × Fin 3))
    (c : Fin 4 → Fin 6 → ℂ),
    (∀ a s t, (∑ x, star (U a s x)*U a t x)=if s=t then 1 else 0) ∧
    (∀ a i j, (∑ y, star (R a i y)*R a j y)=if i=j then 1 else 0) ∧
    (∀ a b, a≠b → ∀ i j,
      Complex.normSq (∑ y, star (R a i y)*R b j y)=(1/3:ℝ)) ∧
    (∀ a b, a≠b →
      (∑ t, ProductGeometry.bloch (U a 0) t*ProductGeometry.bloch (U b 0) t)^2=(1:ℝ)/9) ∧
    (∀ a i, Complex.normSq (c a i)=1) ∧
    (∀ a i x y, B a i x y=c a i*(U a (sigma a i).1 x*R a (sigma a i).2 y))
namespace ProductDirectClassification
open scoped BigOperators
open ProductPhysicalTransport ProductGeometry ProductPhaseRecovery ProductBranchExtraction

noncomputable def qubitBasis (P : NormalizedProductBasis) : Fin 2 → Fin 2 → ℂ :=
  ![P.u 0,qubitPerp (P.u 0)]

theorem qubitBasis_unit (P : NormalizedProductBasis) (s : Fin 2) :
    (∑ x, Complex.normSq (qubitBasis P s x))=1 := by
  fin_cases s
  · simpa [qubitBasis] using P.hu 0
  · change (∑ x, Complex.normSq (qubitPerp (P.u 0) x))=1
    rw [qubitPerp_norm,P.hu]

theorem qubitBasis_orthonormal (P : NormalizedProductBasis) (s t : Fin 2) :
    (∑ x, star (qubitBasis P s x)*qubitBasis P t x)=if s=t then 1 else 0 := by
  have hself (v : Fin 2 → ℂ) (hv : (∑ x, Complex.normSq (v x))=1) :
      (∑ x, star (v x)*v x)=1 := by
    have hh := congrArg (fun r : ℝ => (r:ℂ)) hv
    simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply,Complex.ofReal_one] using hh
  fin_cases s <;> fin_cases t
  · simp only [ite_true]
    change (∑ x, star (qubitBasis P 0 x)*qubitBasis P 0 x)=1
    exact hself (qubitBasis P 0) (qubitBasis_unit P 0)
  · simp [qubitBasis,qubitPerp,Fin.sum_univ_succ] <;> ring
  · simp [qubitBasis,qubitPerp,Fin.sum_univ_succ] <;> ring
  · simp only [ite_true]
    change (∑ x, star (qubitBasis P 1 x)*qubitBasis P 1 x)=1
    exact hself (qubitBasis P 1) (qubitBasis_unit P 1)

theorem original_qubit_phase (P : NormalizedProductBasis) (hP : impurity P=0)
    (i : Fin 6) : ∃ (s : Fin 2) (c : ℂ), Complex.normSq c=1 ∧
      ∀ x, P.u i x=c*qubitBasis P s x := by
  have ha : qubitAxis (P.u 0)=qubitAxis (P.u i) := by
    funext x y
    exact congrFun (zero_impurity_axes_coincide P hP 0 i) (x,y)
  rcases (same_axis_iff_extreme_overlap (P.u 0) (P.u i) (P.hu 0) (P.hu i)).mp ha with hz | ho
  · have hh := qubitPerp_overlap (P.u 0) (P.u i)
    rw [P.hu,P.hu,hz] at hh
    have hp : Complex.normSq (∑ x, star (qubitPerp (P.u 0) x)*P.u i x)=1 := by linarith
    obtain ⟨c,hc,hv⟩ := unit_overlap_phase (P.u i) (qubitPerp (P.u 0)) (P.hu i)
      (by rw [qubitPerp_norm,P.hu]) hp
    exact ⟨1,c,hc,by simpa [qubitBasis] using hv⟩
  · obtain ⟨c,hc,hv⟩ := unit_overlap_phase (P.u i) (P.u 0) (P.hu i) (P.hu 0) ho
    exact ⟨0,c,hc,by simpa [qubitBasis] using hv⟩

theorem original_qutrit_phase
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a : Fin 4) (i : Fin 6) : ∃ (j : Fin 3) (c : ℂ), Complex.normSq c=1 ∧
      ∀ y, (P a).v i y=c*optimalQutritBranches P hopt a j y := by
  obtain ⟨j,hj⟩ := QutritMUBCompleteness.unbiased_three_normSq_one
    (optimalQutritBranches P hopt) (optimalQutritBranches_orthonormal P hopt)
    (optimalQutritBranches_unbiased P hopt) ((P a).v i) ((P a).hv i) a
    (fun b hba j => original_qutrit_unbiased_other_branch P hopt a b hba.symm i j)
  have hu : (∑ y, Complex.normSq (optimalQutritBranches P hopt a j y))=1 := (P a).hv _
  obtain ⟨c,hc,hv⟩ := unit_overlap_phase ((P a).v i)
    (optimalQutritBranches P hopt a j) ((P a).hv i) hu hj
  exact ⟨j,c,hc,hv⟩

theorem normalized_optimum_direct_presentation
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3) :
    HasDirectTetrahedralPresentation (fun a i x y => (P a).u i x*(P a).v i y) := by
  classical
  have hu := (four_optimum_impurity_zero P hopt).1
  have hfactor (a : Fin 4) (i : Fin 6) : ∃ (k : Fin 2 × Fin 3) (c : ℂ),
      Complex.normSq c=1 ∧ ∀ x y, (P a).u i x*(P a).v i y=
        c*(qubitBasis (P a) k.1 x*optimalQutritBranches P hopt a k.2 y) := by
    obtain ⟨s,c,hc,hqubit⟩ := original_qubit_phase (P a) (hu a) i
    obtain ⟨j,d,hd,hqutrit⟩ := original_qutrit_phase P hopt a i
    refine ⟨(s,j),c*d,by rw [Complex.normSq_mul,hc,hd]; norm_num,?_⟩
    intro x y
    rw [hqubit,hqutrit]
    ring
  choose label c hc hf using hfactor
  have hbij (a : Fin 4) : Function.Bijective (label a) := by
    apply orthonormal_phase_labels_bijective
      (show Fintype.card (Fin 6)=Fintype.card (Fin 2 × Fin 3) by decide)
      (fun i (xy : Fin 2 × Fin 3) => (P a).u i xy.1*(P a).v i xy.2)
      (fun k (xy : Fin 2 × Fin 3) => qubitBasis (P a) k.1 xy.1*
        optimalQutritBranches P hopt a k.2 xy.2) (label a) (c a)
    · intro i j
      simpa only [Fintype.sum_prod_type] using (P a).horth i j
    · intro k
      rw [Fintype.sum_prod_type,tensor_norm_factor,qubitBasis_unit]
      have hv : (∑ y, Complex.normSq (optimalQutritBranches P hopt a k.2 y))=1 := (P a).hv _
      rw [hv,one_mul]
    · exact hc a
    · intro i xy
      exact hf a i xy.1 xy.2
  refine ⟨(fun a => qubitBasis (P a)),optimalQutritBranches P hopt,
    (fun a => Equiv.ofBijective (label a) (hbij a)),c,?_,?_,?_,?_,hc,?_⟩
  · exact fun a s t => qubitBasis_orthonormal (P a) s t
  · exact optimalQutritBranches_orthonormal P hopt
  · exact optimalQutritBranches_unbiased P hopt
  · intro a b hab
    simpa [qubitBasis,NormalizedProductBasis.b] using four_optimum_tetrahedral P hopt a b hab
  · exact hf

end ProductDirectClassification

theorem four_product_optimum_direct_presentation
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j=if i=j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y=u x*v y)
    (hopt : productBasisEnergy B=(2:ℝ)/3) : HasDirectTetrahedralPresentation B := by
  have ho : ∀ a i j, productBasisInner B a a i j=
      @ite ℂ (i=j) (Classical.propDecidable (i=j)) 1 0 := by
    intro a i j
    by_cases h : i=j
    · simpa only [if_pos h] using horth a i j
    · simpa only [if_neg h] using horth a i j
  obtain ⟨P,hP⟩ := ProductPhysicalTransport.normalized_bases_from_raw B ho hproduct
  have ht (a b : Fin 4) (i j : Fin 6) :
      ProductPhysicalTransport.productTransition (P a) (P b) i j=
      Complex.normSq (productBasisInner B a b i j) := by
    unfold ProductPhysicalTransport.productTransition productBasisInner
    simp_rw [hP]
  have he : (∑ a, ∑ b, if a<b then ProductPhysicalTransport.pairError (P a) (P b)
      else 0)=(2:ℝ)/3 := by
    simpa only [ProductPhysicalTransport.pairError_eq_centered_squares,ht,
      productBasisEnergy] using hopt
  have hh := ProductDirectClassification.normalized_optimum_direct_presentation P he
  have hB : B=(fun a i x y => (P a).u i x*(P a).v i y) := by
    funext a i x y
    exact hP a i x y
  rw [hB]
  exact hh
namespace ProductPhysicalTransport
open scoped BigOperators

theorem four_optimum_entry_squared_deviation
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 6) :
    (productTransition (P a) (P b) i j-1/6)^2=(1:ℝ)/324 := by
  have hu := (four_optimum_impurity_zero P hopt).1
  have hd := ProductPairEquality.zero_impurity_cross (P a) (P b) (hu a) (hu b) i j
  rw [four_optimum_frameCross P hopt a b hab] at hd
  rw [product_transition_bloch, four_optimum_qutrit_flat P hopt a b hab i j]
  nlinarith only [hd]

theorem four_optimum_entry_deviation
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 6) :
    |productTransition (P a) (P b) i j-1/6|=(1:ℝ)/18 := by
  have h := four_optimum_entry_squared_deviation P hopt a b hab i j
  nlinarith [sq_abs (productTransition (P a) (P b) i j-1/6),
    abs_nonneg (productTransition (P a) (P b) i j-1/6)]

theorem four_optimum_pair_error
    (P : Fin 4 → NormalizedProductBasis)
    (hopt : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) : pairError (P a) (P b)=(1:ℝ)/9 := by
  rw [pairError_eq_centered_squares]
  simp_rw [four_optimum_entry_squared_deviation P hopt a b hab]
  norm_num

theorem raw_optimum_entry_deviation
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j, productBasisInner B a a i j=if i=j then 1 else 0)
    (hproduct : ∀ a i, ∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y, B a i x y=u x*v y)
    (hopt : productBasisEnergy B=(2:ℝ)/3)
    (a b : Fin 4) (hab : a≠b) (i j : Fin 6) :
    |Complex.normSq (productBasisInner B a b i j)-1/6|=(1:ℝ)/18 := by
  classical
  have ho : ∀ a i j, productBasisInner B a a i j=
      @ite ℂ (i=j) (Classical.propDecidable (i=j)) 1 0 := by
    intro a i j
    by_cases h : i=j
    · simpa only [if_pos h] using horth a i j
    · simpa only [if_neg h] using horth a i j
  obtain ⟨P,hP⟩ := normalized_bases_from_raw B ho hproduct
  have ht (a b : Fin 4) (i j : Fin 6) : productTransition (P a) (P b) i j=
      Complex.normSq (productBasisInner B a b i j) := by
    unfold productTransition productBasisInner
    simp_rw [hP]
  have he : (∑ a, ∑ b, if a<b then pairError (P a) (P b) else 0)=(2:ℝ)/3 := by
    simpa only [pairError_eq_centered_squares,ht,productBasisEnergy] using hopt
  simpa only [ht] using four_optimum_entry_deviation P he a b hab i j

end ProductPhysicalTransport

namespace ProductPresentationConverse
open ProductGeometry

theorem unit_of_onb {n : ℕ} (V : Fin n → Fin n → ℂ)
    (hV : ∀ i j,(∑ x,star (V i x)*V j x)=if i=j then 1 else 0)
    (i : Fin n) : (∑ x,Complex.normSq (V i x))=1 := by
  have h := hV i i
  simp only [ite_true] at h
  have hc : ((∑ x,Complex.normSq (V i x)):ℂ)=1 := by
    simpa only [Complex.ofReal_sum,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using h
  exact_mod_cast hc

theorem tetrahedral_qubit_entry (U W : Fin 2 → Fin 2 → ℂ)
    (hU : ∀ i j,(∑ x,star (U i x)*U j x)=if i=j then 1 else 0)
    (hW : ∀ i j,(∑ x,star (W i x)*W j x)=if i=j then 1 else 0)
    (ht : (∑ x,bloch (U 0) x*bloch (W 0) x)^2=(1:ℝ)/9)
    (i j : Fin 2) :
    (Complex.normSq (∑ x,star (U i x)*W j x)/3-(1:ℝ)/6)^2=1/324 := by
  have hu := unit_of_onb U hU
  have hw := unit_of_onb W hW
  have ha : ∀ x,bloch (U 1) x= -bloch (U 0) x :=
    orthogonal_qubits_antipodal (U 1) (U 0) (hu 1) (hu 0) (by simpa using hU 1 0)
  have hb : ∀ x,bloch (W 1) x= -bloch (W 0) x :=
    orthogonal_qubits_antipodal (W 1) (W 0) (hw 1) (hw 0) (by simpa using hW 1 0)
  have hd : (∑ x,bloch (U i) x*bloch (W j) x)^2=(1:ℝ)/9 := by
    fin_cases i <;> fin_cases j
    · exact ht
    · change (∑ x,bloch (U 0) x*bloch (W 1) x)^2=(1:ℝ)/9
      simpa only [hb,mul_neg,Finset.sum_neg_distrib,neg_sq] using ht
    · change (∑ x,bloch (U 1) x*bloch (W 0) x)^2=(1:ℝ)/9
      simpa only [ha,neg_mul,Finset.sum_neg_distrib,neg_sq] using ht
    · change (∑ x,bloch (U 1) x*bloch (W 1) x)^2=(1:ℝ)/9
      simpa only [ha,hb,neg_mul_neg] using ht
  have hp := bloch_overlap (U i) (W j)
  rw [hu,hw,mul_one] at hp
  have he : (Complex.normSq (∑ x,star (U i x)*W j x)/3-(1:ℝ)/6)=
      (∑ x,bloch (U i) x*bloch (W j) x)/6 := by linarith
  rw [he,div_pow,hd]
  norm_num

end ProductPresentationConverse

namespace ProductPresentationConverse

theorem phase_tensor_inner
    (u w : Fin 2 → ℂ) (v z : Fin 3 → ℂ) (c d : ℂ) :
    (∑ x, ∑ y, star (c*(u x*v y))*(d*(w x*z y)))=
      (star c*d)*((∑ x,star (u x)*w x)*(∑ y,star (v y)*z y)) := by
  rw [Finset.sum_mul_sum,Finset.mul_sum]
  simp only [Finset.mul_sum,star_mul]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end ProductPresentationConverse

theorem direct_tetrahedral_presentation_energy
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (h : HasDirectTetrahedralPresentation B) : productBasisEnergy B=(2:ℝ)/3 := by
  classical
  obtain ⟨U,R,sigma,c,hU,hR,hmub,ht,hc,hB⟩ := h
  have hentry (a b : Fin 4) (hab : a≠b) (i j : Fin 6) :
      (Complex.normSq (productBasisInner B a b i j)-(1:ℝ)/6)^2=1/324 := by
    have hinner : productBasisInner B a b i j=
        (star (c a i)*c b j)*
          ((∑ x,star (U a (sigma a i).1 x)*U b (sigma b j).1 x)*
           (∑ y,star (R a (sigma a i).2 y)*R b (sigma b j).2 y)) := by
      simp only [productBasisInner,hB]
      exact ProductPresentationConverse.phase_tensor_inner _ _ _ _ _ _
    rw [hinner]
    have hstar : Complex.normSq (star (c a i))=1 := (Complex.normSq_conj _).trans (hc a i)
    simp only [map_mul,hstar,hc,one_mul,hmub a b hab]
    convert ProductPresentationConverse.tetrahedral_qubit_entry
      (U a) (U b) (hU a) (hU b) (ht a b hab) (sigma a i).1 (sigma b j).1 using 1 <;> ring
  unfold productBasisEnergy
  have hpair (a b : Fin 4) :
      (if a<b then ∑ i,∑ j,(Complex.normSq (productBasisInner B a b i j)-1/6)^2 else 0)=
        if a<b then (1:ℝ)/9 else 0 := by
    by_cases hab : a<b
    · simp only [if_pos hab]
      simp only [hentry a b (ne_of_lt hab)]
      norm_num
    · simp [hab]
  simp_rw [hpair]
  norm_num [Fin.sum_univ_succ]
  norm_num only [Fin.lt_def,Fin.val_zero,Fin.val_one,Fin.val_succ]
  norm_num [show ((2:Fin 3):ℕ)=2 by rfl,show ((2:Fin 4):ℕ)=2 by rfl]


theorem four_product_optimum_iff_direct_presentation
    (B : Fin 4 → Fin 6 → Fin 2 → Fin 3 → ℂ)
    (horth : ∀ a i j,productBasisInner B a a i j=if i=j then 1 else 0)
    (hproduct : ∀ a i,∃ (u : Fin 2 → ℂ) (v : Fin 3 → ℂ),
      ∀ x y,B a i x y=u x*v y) :
    productBasisEnergy B=(2:ℝ)/3 ↔ HasDirectTetrahedralPresentation B :=
  ⟨four_product_optimum_direct_presentation B horth hproduct,
    direct_tetrahedral_presentation_energy B⟩

end
