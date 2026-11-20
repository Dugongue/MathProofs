import EvenP2CropAnchors

namespace EvenTI.TrialProducer

open scoped BigOperators Matrix TensorProduct
open Matrix Mathproof.EvenOrdinaryTISingular

variable {K I J U V : Type*} [Field K]
  [Fintype I] [Fintype J] [Fintype U] [Fintype V] [DecidableEq I] [DecidableEq J]
  [DecidableEq U] [DecidableEq V]

/-- Evaluate a pair of matrix-valued linear projections directly on the rows
of a dense input. Each summand uses one standard coordinate vector. -/
def coordinateProjection (L : (I → K) →ₗ[K] Matrix U U K)
    (R : (J → K) →ₗ[K] Matrix V V K) (A : Matrix I J K) :
    Matrix (U × V) (U × V) K :=
  ∑ i : I, Matrix.kronecker (L (Pi.single i 1)) (R (A i))

private theorem row_expansion (A : Matrix I J K) :
    (∑ i : I, Matrix.vecMulVec (Pi.single i 1) (A i)) = A := by
  ext i j
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.single_apply]

/-- The executable row sum agrees with the chosen tensor-product realization
for every dense input and every pair of linear projections. -/
theorem coordinateProjection_eq (L : (I → K) →ₗ[K] Matrix U U K)
    (R : (J → K) →ₗ[K] Matrix V V K) (A : Matrix I J K) :
    coordinateProjection L R A =
      kroneckerLinearEquiv U U V V K
        (TensorProduct.map L R (matrixTensorEquiv K I J A)) := by
  conv_rhs => rw [← row_expansion A]
  simp only [coordinateProjection, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← matrixTensorEquiv_symm_tmul, LinearEquiv.apply_symm_apply,
    TensorProduct.map_tmul, kroneckerLinearEquiv_tmul]
  rfl

#print axioms coordinateProjection_eq

end EvenTI.TrialProducer
