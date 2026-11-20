import EvenP3RecipHighBatch
import EvenP3RecipHighEvaluation

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (matAnti)
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K I B A L C : Type*} [Field K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C]
variable [DecidableEq I] [DecidableEq B] [DecidableEq A] [DecidableEq L]

def rowEvaluation (T : Matrix I I K →ₗ[K] Matrix I I K) (U : L → Matrix I B K)
    {W : Submodule K (Matrix B I K)} (cols : A → C → W) (y : C → A → L → K) :
    (A → W) →ₗ[K] (A × L → K) :=
  ∑ a : A, (evalTrace (batchVector T U (fun t => primalCombination U (y t a)) cols)).comp
      (W.subtype.comp (LinearMap.proj a : (A → W) →ₗ[K] W))

theorem rowEvaluation_comp_single (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) {W : Submodule K (Matrix B I K)} (cols : A → C → W)
    (y : C → A → L → K) (a : A) :
    (rowEvaluation T U cols y).comp (LinearMap.single K (fun _ : A => W) a) =
      (evalTrace (batchVector T U (fun t => primalCombination U (y t a)) cols)).comp W.subtype := by
  apply LinearMap.ext
  intro v
  simp only [rowEvaluation, LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.proj_apply,
    LinearMap.single_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro a' _ ha
    simp [Pi.single_eq_of_ne ha]
  · simp

theorem rowEvaluation_rank (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) {W : Submodule K (Matrix B I K)} (cols : A → C → W)
    (y : C → A → L → K) (a : A) :
    finrank K (Submodule.span K (Set.range
      (batchVector T U (fun t => primalCombination U (y t a)) cols))) ≤
      finrank K (rowEvaluation T U cols y).range + finrank K (Matrix B I K ⧸ W) := by
  have h := Submodule.finrank_mono (LinearMap.range_comp_le_range
    (LinearMap.single K (fun _ : A => W) a) (rowEvaluation T U cols y))
  rw [rowEvaluation_comp_single] at h
  exact (evalTrace_restricted_rank _ W).trans (Nat.add_le_add_right h _)

/-- Pairing a proposed column kernel vector with a row probe is exactly
one coordinate of the sampled linear coefficient map. -/
theorem rowEvaluation_coeff (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) {W : Submodule K (Matrix B I K)} (cols : A → C → W)
    (y : C → A → L → K) (v : A → W) (p : A × L) :
    rowEvaluation T U cols y v p = ∑ t : C,
      (T (U p.2 * (cols p.1 t).val) *
        (∑ a : A, primalCombination U (y t a) * (v a).val)).trace := by
  simp only [rowEvaluation, LinearMap.sum_apply, Finset.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.subtype_apply, evalTrace_apply, batchVector,
    Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_assoc]
  exact Finset.sum_comm

theorem labelForm_trace (P X Y : Matrix I I K) :
    squarePolar (LinearMap.id : Matrix I I K →ₗ[K] Matrix I I K) (tracePairing P) X Y =
    (matAnti P X * Y).trace := by
  rw [trace_squarePolar_factor]
  rfl

#print axioms rowEvaluation_rank
#print axioms rowEvaluation_coeff
#print axioms labelForm_trace

end
end Mathproof.EvenTI.Reciprocal.Four