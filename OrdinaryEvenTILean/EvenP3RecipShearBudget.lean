import EvenP3RecipFourierLabels
import EvenP1DenseMarginal

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Primary Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.OrderFour
open Mathproof.Problem18FourierCore20260930 (uniformImageWeight)

noncomputable section

variable {K H L J I B : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "Shear" => UpperShear K H L (Option J)

theorem reciprocal_shear_l1_of_label_budget (A : Bases)
    (S : Submodule K (Matrix I I K)) [Fintype S] [Fintype (Module.Dual K S)]
    (hS : ∀ X : Shear, Small.anchor (applyShear X A) - Small.anchor A ∈ S)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (r : Module.Dual K S → ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hr : ∀ m : Module.Dual K S, m ≠ 0 → ∃ c : Module.Dual K (Matrix I I K),
      c.comp S.subtype = m ∧ r m ≤ finrank K (squarePolar (Small.shearDelta A) (traceBlocks c)).range)
    (hSum : (∑ m : Module.Dual K S, if m = 0 then 0 else ((Fintype.card K : ℝ)^r m)⁻¹) ≤ p^2) :
    marginalError (fun X : Shear => (⟨Small.anchor (applyShear X A) - Small.anchor A, hS X⟩ : S)) ≤ p := by
  have hm (X : Shear) : centeredSquare (Small.contraction A) (Small.shearDelta A) Small.partialTraceRight X ∈ S := by
    rw [← Small.anchor_sub]
    exact hS X
  let f := centeredSquareIn S (Small.contraction A) (Small.shearDelta A) Small.partialTraceRight hm
  have he : (fun X : Shear => (⟨Small.anchor (applyShear X A) - Small.anchor A, hS X⟩ : S)) = f := by
    funext X
    exact Subtype.ext (Small.anchor_sub A X)
  rw [he]
  have hFourier := centeredSquare_variation_sq_of_linear_label_ranks S ψ hψ
    (Small.contraction A) (Small.shearDelta A) Small.partialTraceRight hm r (fun m hm => by
      obtain ⟨c, hc, hb⟩ := hr m hm
      rw [traceBlocks_eq_partialTraceRight (J := J)] at hb
      exact ⟨c, hc, hb⟩)
  have hL1 := weight_L1_le_of_fourier_sq f _ (hFourier.trans (div_le_div_of_nonneg_right hSum (by norm_num)))
  refine hL1.trans_eq ?_
  have hr : p^2 / 4 = (p/2)^2 := by ring
  rw [hr, Real.sqrt_sq (by positivity : 0 ≤ p/2)]
  ring

#print axioms reciprocal_shear_l1_of_label_budget

end
end Mathproof.EvenTI.Reciprocal.Coverage
