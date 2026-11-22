import EvenP5PhysicalExecution
import EvenP5EnlargedExecution

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace EvenTI.P15Trial

open EvenTI.TrialProducer Matrix
open scoped BigOperators Matrix

variable {K I J U V : Type*} [Field K]
  [Fintype I] [Fintype J] [Fintype U] [Fintype V] [DecidableEq I] [DecidableEq J]
  [DecidableEq U] [DecidableEq V]

def projectionCoefficients {I U : Type*} [DecidableEq I]
    (L : (I → K) →ₗ[K] Matrix U U K) : Matrix (U×U) I K :=
  fun p i => L (Pi.single i 1) p.1 p.2

/-- A contraction with two separately evaluated matrix projections is one
rectangular three-factor product and a permutation of output coordinates.
The same product routine covers higher and enlarged order-four anchors. -/
theorem coordinateProjection_eq_rectangular
    (L : (I → K) →ₗ[K] Matrix U U K)
    (R : (J → K) →ₗ[K] Matrix V V K) (A : Matrix I J K)
    (u u' : U) (v v' : V) :
    coordinateProjection L R A (u,v) (u',v') =
      (projectionCoefficients L * (A * (projectionCoefficients R)ᵀ)) (u,u') (v,v') := by
  have hR (x : J → K) : R x v v' = ∑ j : J, x j * R (Pi.single j 1) v v' := by
    have hExp : (∑ j : J, x j • Pi.single j 1)=x := by
      ext i
      simp [Finset.sum_apply,Pi.single_apply]
    conv_lhs => rw [← hExp]
    simp only [map_sum,Matrix.sum_apply,map_smul,Matrix.smul_apply,smul_eq_mul]
  simp only [coordinateProjection,Matrix.sum_apply,projectionCoefficients,
    Matrix.mul_apply,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  change L (Pi.single i 1) u u' * R (fun j => A i j) v v' = _
  rw [hR (fun j => A i j)]

#print axioms coordinateProjection_eq_rectangular
end EvenTI.P15Trial
