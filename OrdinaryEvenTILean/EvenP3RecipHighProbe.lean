import EvenP3RecipHighRow
import EvenP1SelectedRows

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.Problem17PolarAssembly (matAnti)
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K I B A L C : Type*} [Field K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C]
variable [DecidableEq I] [DecidableEq B] [DecidableEq A] [DecidableEq L]

private theorem selectedOutputs_unit_probe (U : L → Matrix I B K) (V : A → C → Matrix B I K)
    (p : A × L) (t : C) :
    Coverage.selectedOutputs U V (Pi.single p.1 (Pi.single p.2 1)) t = U p.2 * V p.1 t := by
  unfold Coverage.selectedOutputs
  rw [Finset.sum_eq_single p.1]
  · simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · intro a _ ha
    simp [Pi.single_eq_of_ne ha]
  · simp

private theorem selectedOutputs_row_coeff (U : L → Matrix I B K) (V : A → Unit → Matrix B I K)
    (x : A → L → K) :
    Coverage.selectedOutputs U V x () = ∑ a, primalCombination U (x a) * V a () := by
  simp only [Coverage.selectedOutputs, primalCombination, Matrix.sum_mul, Matrix.smul_mul]

/-- If the physical cross-grid pairing kills a column vector, that vector
is killed by the row evaluation map used in the probability calculation. -/
theorem rowEvaluation_eq_zero_of_cross_test (P : Matrix I I K) (U : L → Matrix I B K)
    {W : Submodule K (Matrix B I K)} (cols : A → C → W) (v : A → W) (y : C → A → L → K)
    (h : ∀ x : A → L → K, (∑ t : C,
       squarePolar LinearMap.id (tracePairing P)
         (Coverage.selectedOutputs U (fun a (_ : Unit) => (v a).val) (y t) ())
         (Coverage.selectedOutputs U (fun a t => (cols a t).val) x t)) = 0) :
    rowEvaluation (matAnti P) U cols y v = 0 := by
  funext p
  have hz := h (Pi.single p.1 (Pi.single p.2 1))
  simp only [selectedOutputs_unit_probe, selectedOutputs_row_coeff] at hz
  have hsym (X Y : Matrix I I K) :
      squarePolar LinearMap.id (tracePairing P) X Y =
        squarePolar LinearMap.id (tracePairing P) Y X := by
    change tracePairing P (X * Y + Y * X) = tracePairing P (Y * X + X * Y)
    rw [add_comm (X * Y)]
  change rowEvaluation (matAnti P) U cols y v p = (0 : K)
  rw [rowEvaluation_coeff]
  convert hz using 1
  apply Finset.sum_congr rfl
  intro t _
  rw [hsym _ (U p.2 * (cols p.1 t).val), labelForm_trace]

#print axioms rowEvaluation_eq_zero_of_cross_test

end
end Mathproof.EvenTI.Reciprocal.Four