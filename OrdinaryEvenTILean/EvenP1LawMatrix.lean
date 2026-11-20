import EvenReciprocalLaw
import Mathlib.LinearAlgebra.Dual.Basis

namespace Mathproof.EvenTI.Reciprocal.Sampling

open Matrix Module
open scoped Matrix

noncomputable section

variable {K R C : Type*} [Field K] [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C]

def pairLinEquiv (x : BasisPairs K R C) : (R → K) ≃ₗ[K] (C → K) :=
  Matrix.toLin'OfInv (M := x.val.2) (M' := x.val.1ᵀ)
    (by simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]
      using congrArg Matrix.transpose x.property.1)
    (by simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]
      using congrArg Matrix.transpose x.property.2)

def basisOfPair (x : BasisPairs K R C) : Basis R K (C → K) :=
  (Pi.basisFun K R).map (pairLinEquiv x)

theorem basisOfPair_apply (x : BasisPairs K R C) (i : R) (j : C) :
    basisOfPair x i j = x.val.1 i j := by
  change (Matrix.toLin' x.val.1ᵀ) ((Pi.basisFun K R) i) j = _
  rw [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rfl

theorem basisOfPair_dual_apply (x : BasisPairs K R C) (i : R) (v : C → K) :
    (basisOfPair x).dualBasis i v = x.val.2 i ⬝ᵥ v := by
  rw [Basis.dualBasis_apply, basisOfPair, Basis.map_repr]
  change (Pi.basisFun K R).repr (Matrix.toLin' x.val.2 v) i = _
  rw [Pi.basisFun_repr, Matrix.toLin'_apply]
  rfl

private def pairOfBasis (b : Basis R K (C → K)) : BasisPairs K R C := by
  let A := LinearMap.toMatrix' b.equivFun.symm.toLinearMap
  let D := LinearMap.toMatrix' b.equivFun.toLinearMap
  have hDA : D * A = (1 : Matrix R R K) := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show b.equivFun.toLinearMap.comp b.equivFun.symm.toLinearMap = LinearMap.id from
      LinearMap.ext b.equivFun.apply_symm_apply]
    exact LinearMap.toMatrix'_one
  have hAD : A * D = (1 : Matrix C C K) := by
    rw [← LinearMap.toMatrix'_comp]
    rw [show b.equivFun.symm.toLinearMap.comp b.equivFun.toLinearMap = LinearMap.id from
      LinearMap.ext b.equivFun.symm_apply_apply]
    exact LinearMap.toMatrix'_one
  refine ⟨(Aᵀ, D), ?_, ?_⟩
  · rw [← Matrix.transpose_mul, hDA, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, hAD, Matrix.transpose_one]

private theorem basis_coordinates_single (b : Basis R K (C → K)) (i : R) :
    b.equivFun.symm (Pi.single i 1) = b i := by
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  rw [Basis.equivFun_self, Pi.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

def basisPairsEquiv : BasisPairs K R C ≃ Basis R K (C → K) where
  toFun := basisOfPair
  invFun := pairOfBasis
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · ext i j
      change LinearMap.toMatrix' (basisOfPair x).equivFun.symm.toLinearMap j i = _
      rw [LinearMap.toMatrix'_apply]
      change (basisOfPair x).equivFun.symm (Pi.single i 1) j = _
      rw [basis_coordinates_single, basisOfPair_apply]
    · ext i j
      change LinearMap.toMatrix' (basisOfPair x).equivFun.toLinearMap i j = _
      rw [LinearMap.toMatrix'_apply]
      change (basisOfPair x).repr (Pi.single j 1) i = _
      rw [← Basis.dualBasis_apply, basisOfPair_dual_apply, dotProduct_single_one]
  right_inv b := by
    apply DFunLike.ext
    intro i
    funext j
    rw [basisOfPair_apply]
    change LinearMap.toMatrix' b.equivFun.symm.toLinearMap j i = _
    rw [LinearMap.toMatrix'_apply]
    change b.equivFun.symm (Pi.single i 1) j = _
    exact congrFun (basis_coordinates_single b i) j

#print axioms basisOfPair_apply
#print axioms basisOfPair_dual_apply
#print axioms basisPairsEquiv

end
end Mathproof.EvenTI.Reciprocal.Sampling
