import EvenP3RecipHighLaw
import EvenP3RecipHighProbe
import EvenP3RecipHighRectangle

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.PartOne (rectDual)
open Mathproof.EvenTI.Reciprocal.Sampling
open Mathproof.Problem17PolarAssembly (matAnti)
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K H L J I B BL A C R : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B] [Fintype BL]
variable [Fintype A] [Fintype C] [Fintype R]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]
variable [DecidableEq BL] [DecidableEq A] [DecidableEq C] [DecidableEq R]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option J) (I := I) (B := B)
local notation "T" => (traceKernel (K := K) (I := I))

abbrev liveHighDual {a : ℕ} (U : Bases) (hi : Fin a ↪ H) (lo : BL ↪ L)
    (z : Fin a × J) : matrixAnnihilator (actualRows U hi lo).1.val :=
  (matrixAnnihilatorEquiv (actualRows U hi lo).1.val).symm ((actualRows U hi lo).2.val z)

theorem liveHighDual_val {a : ℕ} (U : Bases) (hi : Fin a ↪ H) (lo : BL ↪ L)
    (z : Fin a × J) : (liveHighDual U hi lo z).val = Coverage.selectedDual U hi z.1 z.2 := by
  change rectDual.symm ((actualRows U hi lo).2.val z).val = _
  rw [actualRows_dual, LinearEquiv.symm_apply_apply]

def columnPool {a : ℕ} {W : Type*} (eA : A ≃ Fin a) (e : C ⊕ R ≃ J)
    (D : Fin a × J → W) (i : A) (t : C) : W := D (eA i, e (.inl t))

def rowPool {a : ℕ} {W : Type*} (eA : A ≃ Fin a) (e : C ⊕ R ≃ J)
    (D : Fin a × J → W) (t : R) (i : A) : W := D (eA i, e (.inr t))

/-- A live selected sample passing the independent-row coefficient test
certifies the corresponding high label on the original physical shear. -/
theorem physical_rank_of_high_model_good {a : ℕ} (U : Bases) (hi : Fin a ↪ H) (lo : BL ↪ L)
    (eA : A ≃ Fin a) (e : C ⊕ R ≃ J) (P : Matrix I I K)
    (h : ∀ y : C → A → BL → K, (∀ t : R, rowEvaluation (matAnti P) (actualRows U hi lo).1.val
      (columnPool eA e (liveHighDual U hi lo)) y (rowPool eA e (liveHighDual U hi lo) t) = 0) → y = 0) :
    finrank K (C → A → BL → K) - (Fintype.card I)^2 ≤
      finrank K (squarePolar (deltaLinear (matrixPrimal U.val.1) (matrixDual U.val.2))
        (traceBlocks (tracePairing P))).range := by
  let p := (actualRows U hi lo).1.val
  let d := liveHighDual U hi lo
  let hi' := eA.toEmbedding.trans hi
  have hp : p = Coverage.selectedPrimal U lo := funext (actualRows_primal U hi lo)
  have hiD (i : A) (t : J) : Coverage.selectedDual U hi' i t = (d (eA i,t)).val := by
    rw [liveHighDual_val]
    rfl
  have hphys := reciprocal_polar_rank_of_selected_cross_groups U e hi' lo (tracePairing P)
  have hcorrect : finrank K (labelForm T (tracePairing P)).range ≤ (Fintype.card I)^2 := by
    refine (Submodule.finrank_le _).trans ?_
    rw [Subspace.dual_finrank_eq]
    exact (Submodule.finrank_le _).trans_eq (by simp [Module.finrank_matrix, pow_two])
  have hcross : ∀ y : C → A → BL → K,
      (∀ (t : R) (x : A → BL → K), (∑ u : C, labelForm T (tracePairing P)
        (selectedReciprocalBlock U (e (.inr t)) (extendRectangle hi' lo (y u)))
        (selectedReciprocalBlock U (e (.inl u)) (extendRectangle hi' lo x))) = 0) → y = 0 := by
    intro y hz
    apply h y
    intro t
    apply rowEvaluation_eq_zero_of_cross_test
    intro x
    have he (u : C) : labelForm T (tracePairing P)
        (selectedReciprocalBlock U (e (.inr t)) (extendRectangle hi' lo (y u)))
        (selectedReciprocalBlock U (e (.inl u)) (extendRectangle hi' lo x)) =
      squarePolar LinearMap.id (tracePairing P)
        (Coverage.selectedOutputs p (fun i (_ : Unit) => (rowPool eA e d t i).val) (y u) ())
        (Coverage.selectedOutputs p (fun i j => (columnPool eA e d i j).val) x u) := by
      change squarePolar LinearMap.id (tracePairing P)
        (selectedReciprocalBlock U (e (.inr t)) (extendRectangle hi' lo (y u))).val
        (selectedReciprocalBlock U (e (.inl u)) (extendRectangle hi' lo x)).val = _
      rw [selected_block_apply, selected_block_apply, hp]
      simp only [Coverage.selectedOutputs, rowPool, columnPool, hiD]
    simpa only [he] using hz t x
  have hsub : finrank K (C → A → BL → K) - (Fintype.card I)^2 ≤
      finrank K (C → A → BL → K) - finrank K (labelForm T (tracePairing P)).range := by omega
  exact hsub.trans (hphys hcross)

#print axioms liveHighDual_val
#print axioms physical_rank_of_high_model_good

end
end Mathproof.EvenTI.Reciprocal.Four