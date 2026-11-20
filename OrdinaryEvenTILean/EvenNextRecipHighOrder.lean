import EvenNextRecipTrace
import EvenNextRecipLabels
import EvenNextRecipScale
import EvenReciprocalAnchorSmall

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal
open Mathproof.Problem17TracePairing

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)

theorem baseline_row_trace_zero (A : Bases) (t : J) (x : H → L → K) :
    rowLinear (matrixPrimal A.val.1) (matrixDual A.val.2) t x ∈ traceKernel := by
  change ((rowLinear (matrixPrimal A.val.1) (matrixDual A.val.2) t) x).trace = 0
  have h : rowLinear (matrixPrimal A.val.1) (matrixDual A.val.2) t x =
      (fun i j => oneRow (matrixPrimal A.val.1) (matrixDual A.val.2) x t i j) := by
    ext i j
    exact rowLinear_apply _ _ _ _ _ _
  rw [h]
  exact oneRow_reciprocal_trace_zero A x t

def baselineRows (A : Bases) : (H → L → K) →ₗ[K] (J → traceKernel (K := K) (I := I)) :=
  rowsLinear (matrixPrimal A.val.1) (matrixDual A.val.2) traceKernel (baseline_row_trace_zero A)

private theorem baseline_label_polar_rank (A : Bases)
    (hJ : Fintype.card J = Fintype.card I - 1) (hI : 8 ≤ Fintype.card I)
    (hA : Function.Surjective (baselineRows A))
    (c : Module.Dual K (Matrix I I K))
    (hc : Fintype.card I - 2 ≤ finrank K (labelForm traceKernel c).range) :
    4 * Fintype.card I ^ 2 ≤ finrank K
      (squarePolar (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)) (traceBlocks c)).range := by
  have hlow := shear_polar_rank (matrixPrimal A.val.1) (matrixDual A.val.2)
    traceKernel (baseline_row_trace_zero A) c hA
  calc
    _ ≤ ((Fintype.card I - 1) ^ 2 - 1) * (Fintype.card I - 2) :=
      reciprocal_rank_arithmetic _ hI
    _ ≤ (Fintype.card J ^ 2 - 1) * finrank K (labelForm traceKernel c).range := by
      rw [hJ]
      exact Nat.mul_le_mul_left _ hc
    _ ≤ _ := hlow

/-- A surjective selected row map for actual reciprocal bases implies the
needed full-shear polar rank for every label nontrivial on trace zero. -/
theorem baseline_traceZero_polar_rank [Nonempty I] (A : Bases)
    (hJ : Fintype.card J = Fintype.card I - 1) (hI : 8 ≤ Fintype.card I)
    (hA : Function.Surjective (baselineRows A))
    (c : Module.Dual K (Matrix I I K))
    (hc : c.comp (traceKernel (K := K) (I := I)).subtype ≠ 0) :
    4 * Fintype.card I ^ 2 ≤ finrank K
      (squarePolar (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)) (traceBlocks c)).range :=
  baseline_label_polar_rank A hJ hI hA c (traceZero_label_rank c hc)

/-- In odd characteristic the same estimate also covers scalar labels. -/
theorem baseline_odd_polar_rank [Nonempty I] (A : Bases)
    (hJ : Fintype.card J = Fintype.card I - 1) (hI : 8 ≤ Fintype.card I)
    (hA : Function.Surjective (baselineRows A))
    (P : Matrix I I K) (hP : P ≠ 0) (h₂ : (2 : K) ≠ 0) :
    4 * Fintype.card I ^ 2 ≤ finrank K
      (squarePolar (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2))
        (traceBlocks (tracePairing P))).range :=
  baseline_label_polar_rank A hJ hI hA _ (traceZero_odd_label_rank P hP h₂)

theorem traceBlocks_eq_partialTraceRight (c : Module.Dual K (Matrix I I K)) :
    traceBlocks (J := J) c = c.comp Small.partialTraceRight := by
  apply LinearMap.ext
  intro A
  simp only [traceBlocks, LinearMap.sum_apply, LinearMap.comp_apply]
  rw [← map_sum]
  congr 1
  ext i j
  simp only [Matrix.sum_apply]
  rfl

theorem anchor_difference_mem_traceKernel [CharP K 2] (A : Bases) (X : UpperShear K H L (Option J)) :
    Small.anchor (applyShear X A) - Small.anchor A ∈ traceKernel := by
  rw [Small.anchor_sub]
  exact Small.centered_mem_traceZero A X

open Mathproof.Problem18FourierCore20260930 (uniformImageWeight)

theorem highOrder_anchor_variation_sq_charTwo [CharP K 2] [Fintype K] [Nonempty I]
    [Fintype (traceKernel (K := K) (I := I))]
    (A : Bases) (hJ : Fintype.card J = Fintype.card I - 1) (hI : 8 ≤ Fintype.card I)
    (hA : Function.Surjective (baselineRows A)) (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    ((∑ y, ‖uniformImageWeight
      (fun X : UpperShear K H L (Option J) =>
        (⟨Small.anchor (applyShear X A) - Small.anchor A, anchor_difference_mem_traceKernel A X⟩ :
          traceKernel (K := K) (I := I))) y -
      (Fintype.card (traceKernel (K := K) (I := I)) : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card (traceKernel (K := K) (I := I)) : ℝ) *
        ((Fintype.card K : ℝ)^(4 * Fintype.card I ^ 2))⁻¹ / 4 := by
  refine Small.anchor_variation_sq A traceKernel (anchor_difference_mem_traceKernel A) ψ hψ _ ?_
  intro c hc
  rw [← traceBlocks_eq_partialTraceRight]
  exact baseline_traceZero_polar_rank A hJ hI hA c hc

#print axioms baseline_traceZero_polar_rank
#print axioms baseline_odd_polar_rank
#print axioms highOrder_anchor_variation_sq_charTwo

end Mathproof.EvenTI.Reciprocal.Next

