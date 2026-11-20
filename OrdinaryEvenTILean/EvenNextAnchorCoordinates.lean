import EvenNextAnchorMatrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Choose coordinates of the *image of the restricted projection*, and
extend those coordinates to a concrete matrix on the ambient input. -/
namespace Mathproof.EvenOrdinaryTISingular

open Matrix Module
noncomputable section

variable {K M V : Type*} [Field K] [Fintype M] [DecidableEq M]
  [AddCommGroup V] [Module K V] [Module.Finite K V]

def restrictToImage (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    L →ₗ[K] L.map p :=
  (p.comp L.subtype).codRestrict _ (fun x => Submodule.mem_map.mpr ⟨x.val, x.property, rfl⟩)

theorem restrictToImage_surjective (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    Function.Surjective (restrictToImage L p) := by
  intro y
  obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.property
  exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

def basisOfCrop (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    L.map p ≃ₗ[K] (Fin (finrank K (L.map p)) → K) :=
  (Module.finBasis K (L.map p)).equivFun

def cropCoordinates (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    L →ₗ[K] (Fin (finrank K (L.map p)) → K) :=
  (basisOfCrop L p).toLinearMap.comp (restrictToImage L p)

theorem cropCoordinates_surjective (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    Function.Surjective (cropCoordinates L p) :=
  (basisOfCrop L p).surjective.comp (restrictToImage_surjective L p)

/-- Extend the coordinates chosen on the restricted image to ordinary input
coordinates. The crop only reads the restriction, verified below. -/
def coordinateCropMatrix (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    Matrix (Fin (finrank K (L.map p))) M K :=
  LinearMap.toMatrix' (cropCoordinates L p).exists_extend.choose

theorem coordinateCropMatrix_restrict (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    (coordinateCropMatrix L p).toLin'.comp L.subtype = cropCoordinates L p := by
  rw [coordinateCropMatrix, Matrix.toLin'_toMatrix']
  exact (cropCoordinates L p).exists_extend.choose_spec

theorem coordinateCropMatrix_surjective (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) :
    Function.Surjective ((coordinateCropMatrix L p).toLin'.comp L.subtype) := by
  rw [coordinateCropMatrix_restrict]
  exact cropCoordinates_surjective L p

/-- A coordinate returned by the crop decodes to the value of the original
projection on the opposite annihilator. -/
theorem coordinateCropMatrix_decodes (L : Submodule K (M → K)) (p : (M → K) →ₗ[K] V) (x : L) :
    ((basisOfCrop L p).symm ((coordinateCropMatrix L p).toLin' x.val) : V) = p x.val := by
  have h := LinearMap.congr_fun (coordinateCropMatrix_restrict L p) x
  change (coordinateCropMatrix L p).toLin' x.val =
    basisOfCrop L p (restrictToImage L p x) at h
  rw [h, LinearEquiv.symm_apply_apply]
  rfl

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.coordinateCropMatrix_surjective
#print axioms Mathproof.EvenOrdinaryTISingular.coordinateCropMatrix_decodes
