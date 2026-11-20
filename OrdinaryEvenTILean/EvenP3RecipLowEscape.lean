import EvenNextRecipLabels
import Mathlib.LinearAlgebra.Matrix.Bilinear

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped Matrix
open Matrix Module LinearMap
open Mathproof.Problem17PolarAssembly (matAnti matAnti_apply)

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq I]

/-- Each independent pair of source and image vectors contributes a complete
matrix row to the anticommutator rank. -/
theorem anticommutator_rank_ge_of_escape (P : Matrix I I K) (U : Matrix I J K)
    (hu : Function.Injective
      (fun x : (J → K) × (J → K) => U *ᵥ x.1 + (P * U) *ᵥ x.2)) :
    Fintype.card I * Fintype.card J ≤ finrank K (matAnti P).range := by
  let f : Matrix J I K →ₗ[K] Matrix I I K :=
    (matAnti P).comp (mulLeftLinearMap I K U)
  have hf (X : Matrix J I K) (j : I) :
      (f X).col j = U *ᵥ (X * P).col j + (P * U) *ᵥ X.col j := by
    change (P * (U * X) + (U * X) * P).col j = _
    rw [← Matrix.mul_assoc P U X, Matrix.mul_assoc U X P, add_comm] <;> rfl
  have hi : Function.Injective f := by
    intro X Y he
    ext i j
    have hh := congrArg (fun Z : Matrix I I K => Z.col j) he
    rw [hf, hf] at hh
    have hxy : ((X * P).col j, X.col j) = ((Y * P).col j, Y.col j) := hu hh
    exact congrFun (congrArg Prod.snd hxy) i
  have hle : finrank K f.range ≤ finrank K (matAnti P).range :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  rwa [LinearMap.finrank_range_of_inj hi, Module.finrank_matrix, Module.finrank_self,
    mul_one, Nat.mul_comm] at hle

#print axioms anticommutator_rank_ge_of_escape

end Mathproof.EvenTI.Reciprocal.SquareLow
