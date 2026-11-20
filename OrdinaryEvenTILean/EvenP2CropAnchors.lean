import EvenP2CropLiteral
import EvenP2PolarOperators

namespace Mathproof.EvenOrdinaryTISingular
open scoped Matrix TensorProduct
open Matrix Module EvenTI.Action EvenTI.AnchorCovariance
noncomputable section
variable {K : Type*} [Field K] {l r n : ℕ}

/-- Take the square and the two partial traces after the literal physical
kernel projection, without reference to chosen image coordinates. -/
def literalSingularAnchors
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : Tensor K ((l + 1) + (r + 1)) n) :
    PhysicalMatrix K n × PhysicalMatrix K n :=
  let Z := kroneckerLinearEquiv (Fin n) (Fin n) (Fin n) (Fin n) K
    (literalSingularProjection i j ell rho A)
  (partialTraceLeft (Z ^ 2), partialTraceRight (Z ^ 2))

/-- The covariants on the decoded image tensor are the two squared partial
traces of the literal projection. -/
theorem rawSingularCrop_covariants_eq_literal
    (R : Submodule K (Coord (r + 1) n → K))
    (S : Submodule K (Coord (l + 1) n → K))
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (hS : physicalMatrixImage S i ell ≤ PolarOperator.TraceZero K (Fin n))
    (hR : physicalMatrixImage R j rho ≤ PolarOperator.TraceZero K (Fin n))
    (A : DenseKernelFiber R S) :
    (PolarOperator.covariants
      (TensorProduct.map (Submodule.inclusion hS) (Submodule.inclusion hR)
        (rawSingularCrop R S i j ell rho A))).val =
      literalSingularAnchors i j ell rho A.val := by
  let x := rawSingularCrop R S i j ell rho A
  let a := TensorProduct.map (Submodule.inclusion hS) (Submodule.inclusion hR) x
  let Z := kroneckerLinearEquiv (Fin n) (Fin n) (Fin n) (Fin n) K
    (literalSingularProjection i j ell rho A.val)
  have hw : PolarOperator.embed a = Z := by
    change kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (PolarOperator.TraceZero K (Fin n)).subtype
        (PolarOperator.TraceZero K (Fin n)).subtype
        (TensorProduct.map (Submodule.inclusion hS) (Submodule.inclusion hR) x)) = _
    rw [TensorProduct.map_map]
    change kroneckerLinearEquiv _ _ _ _ K
      (TensorProduct.map (physicalMatrixImage S i ell).subtype
        (physicalMatrixImage R j rho).subtype x) = _
    exact congrArg (kroneckerLinearEquiv (Fin n) (Fin n) (Fin n) (Fin n) K)
      (rawSingularCrop_embedded_eq R S i j ell rho A)
  change (partialTraceLeft (PolarOperator.embed a ^ 2),
    partialTraceRight (PolarOperator.embed a ^ 2)) = _
  rw [hw] <;> rfl

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.rawSingularCrop_covariants_eq_literal
