import EvenReciprocalLaw
import EvenReciprocalFourier
import Mathlib.Algebra.CharP.Frobenius

/-! Characteristic-dependent affine targets for the reciprocal anchor. -/
namespace Mathproof.EvenTI.Reciprocal.Small
open scoped BigOperators Matrix
open Matrix
open Mathproof.EvenTI.Reciprocal
open Mathproof.Problem18FourierCore20260930 (uniformImageWeight)

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := J) (I := I) (B := B)

/-- The right partial-trace map from the Problem 1.8 development. -/
def partialTraceRight : Matrix (J × I) (J × I) K →ₗ[K] Matrix I I K where
  toFun X a b := ∑ c, X (c,a) (c,b)
  map_add' X Y := by
    ext a b
    exact Finset.sum_add_distrib
  map_smul' k X := by
    ext a b
    exact Finset.mul_sum _ _ _ |>.symm

/-- The diagonal and off-diagonal argument of the checked Problem 1.7
QuadraticCovariants module, isolated here to avoid importing its large
algorithm development. -/
private theorem trace_square_charTwo {i : Type*} [Fintype i] [DecidableEq i]
    [CharP K 2] (Z : Matrix i i K) :
    Matrix.trace (Z ^ 2) = (Matrix.trace Z) ^ 2 := by
  classical
  let f : i × i → K := fun p => if p.1 = p.2 then 0 else Z p.1 p.2 * Z p.2 p.1
  have htwo : (2 : K) = 0 := by exact CharP.cast_eq_zero K 2
  have hoff : ∑ p, f p = 0 := by
    apply Finset.sum_involution (fun p _ => p.swap)
    · rintro ⟨a,b⟩ _
      by_cases hab : a = b
      · simp [f, hab]
      · simp only [f, Prod.swap_prod_mk, if_neg hab, if_neg (Ne.symm hab), mul_comm (Z b a)]
        rw [← two_mul, htwo, zero_mul]
    · rintro ⟨a,b⟩ _ hf hs
      have hba : b = a := congrArg Prod.fst hs
      subst b
      exact hf (by simp [f])
    · intro p hp
      simp
    · intro p hp
      simp
  have hsplit (p : i × i) :
      Z p.1 p.2 * Z p.2 p.1 = f p + if p.1 = p.2 then Z p.1 p.1 ^ 2 else 0 := by
    rcases p with ⟨a,b⟩
    by_cases hab : a = b <;> simp [f, hab, pow_two]
  calc
    Matrix.trace (Z ^ 2) = ∑ p : i × i, Z p.1 p.2 * Z p.2 p.1 := by
      simp only [pow_two, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
    _ = ∑ a, Z a a ^ 2 := by
      simp only [hsplit, Finset.sum_add_distrib, hoff, zero_add]
      simp [Fintype.sum_prod_type]
    _ = (Matrix.trace Z) ^ 2 := by
      change (∑ a, frobenius K 2 (Z a a)) = frobenius K 2 (∑ a, Z a a)
      exact (map_sum _ _ _).symm

def contraction (A : Bases) : Matrix (J × I) (J × I) K :=
  crossed (matrixPrimal A.val.1) (matrixDual A.val.2)

def anchor (A : Bases) : Matrix I I K := partialTraceRight (contraction A ^ 2)

theorem trace_contraction (A : Bases) :
    (contraction A).trace = (Fintype.card (Sum H L × J) : K) := by
  have hs : (contraction A).trace = (A.val.1 * A.val.2ᵀ).trace := by
    simp only [contraction, Matrix.trace, Matrix.diag, crossed, Matrix.mul_apply,
      matrixPrimal, matrixDual, Matrix.transpose_apply, Fintype.sum_prod_type]
    calc
      _ = ∑ j : J, ∑ a : Sum H L, ∑ i : I, ∑ b : B, A.val.1 (a,j) (i,b) * A.val.2 (a,j) (i,b) :=
        Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hs, A.property.1, Matrix.trace_one]

theorem trace_partialTraceRight (Z : Matrix (J × I) (J × I) K) :
    (partialTraceRight Z).trace = Z.trace := by
  change (∑ i : I, ∑ j : J, Z (j,i) (j,i)) = ∑ p : J × I, Z p p
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem trace_anchor_charTwo [CharP K 2] (A : Bases) :
    (anchor A).trace = (Fintype.card (Sum H L × J) : K)^2 := by
  rw [anchor, trace_partialTraceRight, trace_square_charTwo, trace_contraction]

def shearDelta (A : Bases) : UpperShear K H L J →ₗ[K] Matrix (J × I) (J × I) K :=
  deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)

theorem anchor_sub (A : Bases) (X : UpperShear K H L J) :
    anchor (applyShear X A) - anchor A =
      centeredSquare (contraction A) (shearDelta A) partialTraceRight X := by
  have h : contraction (applyShear X A) = contraction A + shearDelta A X :=
    crossed_matrix_shear A.val.1 A.val.2 X
  simp [anchor, h, centeredSquare]

def traceZero : Submodule K (Matrix I I K) :=
  (Matrix.traceLinearMap (α := K) I K).ker

theorem centered_mem_traceZero [CharP K 2] (A : Bases) (X : UpperShear K H L J) :
    centeredSquare (contraction A) (shearDelta A) partialTraceRight X ∈ traceZero := by
  rw [← anchor_sub]
  change (anchor (applyShear X A) - anchor A).trace = 0
  rw [Matrix.trace_sub, trace_anchor_charTwo, trace_anchor_charTwo, sub_self]

theorem anchor_variation_sq (A : Bases) [Fintype K]
    (S : Submodule K (Matrix I I K)) [Fintype S]
    (hS : ∀ X : UpperShear K H L J, anchor (applyShear X A) - anchor A ∈ S)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (r : ℕ)
    (hr : ∀ c : Module.Dual K (Matrix I I K), c.comp S.subtype ≠ 0 →
      r ≤ Module.finrank K (squarePolar (shearDelta A) (c.comp partialTraceRight)).range) :
    ((∑ y, ‖uniformImageWeight
      (fun X : UpperShear K H L J => (⟨anchor (applyShear X A) - anchor A, hS X⟩ : S)) y -
      (Fintype.card S : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card S : ℝ) * ((Fintype.card K : ℝ)^r)⁻¹ / 4 := by
  have hm (X : UpperShear K H L J) :
      centeredSquare (contraction A) (shearDelta A) partialTraceRight X ∈ S := by
    rw [← anchor_sub]
    exact hS X
  have he : (fun X : UpperShear K H L J => (⟨anchor (applyShear X A) - anchor A, hS X⟩ : S)) =
      centeredSquareIn S (contraction A) (shearDelta A) partialTraceRight hm := by
    funext X
    exact Subtype.ext (anchor_sub A X)
  rw [he]
  exact centeredSquare_variation_sq S ψ hψ r _ _ _ hm hr

end Mathproof.EvenTI.Reciprocal.Small

#print axioms Mathproof.EvenTI.Reciprocal.Small.trace_anchor_charTwo
#print axioms Mathproof.EvenTI.Reciprocal.Small.anchor_variation_sq
