import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Dual.Lemmas
import EvenLiveSingularKernels

/-! Coordinate transpose kernels and the exact two-kernel fiber. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module
open scoped Matrix
noncomputable section

variable {K M N : Type*} [Field K] [Fintype M] [Fintype N]
  [DecidableEq M] [DecidableEq N]

theorem dualMap_dotProductEquiv (A : Matrix M N K) (x : M → K) :
    A.toLin'.dualMap (dotProductEquiv K M x) =
      dotProductEquiv K N (Aᵀ.toLin' x) := by
  apply LinearMap.ext
  intro v
  change x ⬝ᵥ (A *ᵥ v) = (Aᵀ *ᵥ x) ⬝ᵥ v
  rw [dotProduct_comm (Aᵀ *ᵥ x) v, dotProduct_transpose_mulVec]

theorem dualKernel_comap_dotProductEquiv (A : Matrix M N K) :
    A.toLin'.dualMap.ker.comap (dotProductEquiv K M).toLinearMap = Aᵀ.toLin'.ker := by
  ext x
  simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_coe,
    dualMap_dotProductEquiv]
  exact (dotProductEquiv K N).map_eq_zero_iff

theorem dualKernel_eq_map_transpose (A : Matrix M N K) :
    A.toLin'.dualMap.ker = Aᵀ.toLin'.ker.map (dotProductEquiv K M).toLinearMap := by
  rw [← dualKernel_comap_dotProductEquiv A]
  exact (Submodule.map_comap_eq_of_surjective (dotProductEquiv K M).surjective _).symm

/-- The exact left-coordinate kernel associated to an image subspace. -/
def coordinateLeftKernel (L : Submodule K (M → K)) : Submodule K (M → K) :=
  L.dualAnnihilator.comap (dotProductEquiv K M).toLinearMap

/-- Any prescribed coordinate left kernel determines an image subspace. -/
def imageFromLeftKernel (S : Submodule K (M → K)) : Submodule K (M → K) :=
  (S.map (dotProductEquiv K M).toLinearMap).dualCoannihilator

theorem coordinateLeftKernel_imageFromLeftKernel (S : Submodule K (M → K)) :
    coordinateLeftKernel (imageFromLeftKernel S) = S := by
  unfold coordinateLeftKernel imageFromLeftKernel
  rw [Subspace.dualCoannihilator_dualAnnihilator_eq]
  exact Submodule.comap_map_eq_of_injective (dotProductEquiv K M).injective S

theorem transposeKernel_eq_iff_dualKernel_eq (A : Matrix M N K)
    (L : Submodule K (M → K)) :
    Aᵀ.toLin'.ker = coordinateLeftKernel L ↔ A.toLin'.dualMap.ker = L.dualAnnihilator := by
  constructor
  · intro h
    rw [dualKernel_eq_map_transpose, h, coordinateLeftKernel]
    exact Submodule.map_comap_eq_of_surjective (dotProductEquiv K M).surjective _
  · intro h
    rw [← dualKernel_comap_dotProductEquiv A, h]
    rfl

abbrev MatrixKernelFiber (R : Submodule K (N → K)) (S : Submodule K (M → K)) :=
  {A : Matrix M N K // A.toLin'.ker = R ∧ Aᵀ.toLin'.ker = S}

/-- Matrix coordinates identify the actual right and transpose-kernel fiber
bijectively with the exact two-kernel linear-map fiber. -/
def matrixTwoKernelsEquiv (R : Submodule K (N → K)) (L : Submodule K (M → K)) :
    MatrixKernelFiber R (coordinateLeftKernel L) ≃ TwoKernels R L.dualAnnihilator :=
  Matrix.toLin'.toEquiv.subtypeEquiv fun A =>
    and_congr_right fun _ => transposeKernel_eq_iff_dualKernel_eq A L

@[simp] theorem matrixTwoKernelsEquiv_apply_val
    (R : Submodule K (N → K)) (L : Submodule K (M → K))
    (A : MatrixKernelFiber R (coordinateLeftKernel L)) :
    (matrixTwoKernelsEquiv R L A).val = A.val.toLin' := rfl

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.dualKernel_eq_map_transpose
#print axioms Mathproof.EvenOrdinaryTISingular.coordinateLeftKernel_imageFromLeftKernel
#print axioms Mathproof.EvenOrdinaryTISingular.matrixTwoKernelsEquiv
