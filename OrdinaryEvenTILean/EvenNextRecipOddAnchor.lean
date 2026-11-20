import EvenNextRecipHighOrder

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal
open Mathproof.Problem17TracePairing
open Mathproof.Problem18FourierCore20260930 (uniformImageWeight)

variable {K H L J I B : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)

local notation "Full" => (⊤ : Submodule K (Matrix I I K))

/-- Under the same row-surjectivity event, the odd-characteristic squared
variation estimate compares the shear image with the full matrix space. -/
theorem highOrder_anchor_variation_sq_odd [Fintype K] [Nonempty I] [Fintype (↥Full)]
    (A : Bases) (hJ : Fintype.card J = Fintype.card I - 1) (hI : 8 ≤ Fintype.card I)
    (hA : Function.Surjective (baselineRows A)) (h₂ : (2 : K) ≠ 0)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) :
    ((∑ y, ‖uniformImageWeight
      (fun X : UpperShear K H L (Option J) =>
        (⟨Small.anchor (applyShear X A) - Small.anchor A, Submodule.mem_top⟩ : Full)) y -
      (Fintype.card (↥Full) : ℂ)⁻¹‖) / 2)^2 ≤
      (Fintype.card (↥Full) : ℝ) *
        ((Fintype.card K : ℝ)^(4 * Fintype.card I ^ 2))⁻¹ / 4 := by
  refine Small.anchor_variation_sq A Full (fun _ => Submodule.mem_top) ψ hψ _ ?_
  intro c hc
  obtain ⟨P, hP⟩ :=
    ((tracePairing (K := K) (ι := I)).toDual tracePairing_nondegenerate).surjective c
  change tracePairing P = c at hP
  have hP0 : P ≠ 0 := by
    intro hz
    apply hc
    rw [← hP, hz]
    simp
  rw [← traceBlocks_eq_partialTraceRight, ← hP]
  exact baseline_odd_polar_rank A hJ hI hA P hP0 h₂

#print axioms highOrder_anchor_variation_sq_odd

end Mathproof.EvenTI.Reciprocal.Next
