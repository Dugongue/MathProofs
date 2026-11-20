import EvenP5KernelScan
import Mathlib.FieldTheory.Finite.Basic

/-! Compute the Frobenius-fixed vectors using the checked Part 5 row kernel.
The coordinate matrices are formed directly from multiplication in the input
finite commutative algebra. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open Matrix EvenTI.Contract

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] {d : ℕ}

/-- The difference of the (q)-Frobenius and identity in storage coordinates. -/
def fixedDifference (C : A ≃ₗ[K] (Fin d → K)) : (Fin d → K) →ₗ[K] (Fin d → K) :=
  C.toLinearMap.comp
    (((FiniteField.frobeniusAlgHom K A).toLinearMap - LinearMap.id).comp C.symm.toLinearMap)

abbrev fixedSpace (K A : Type) [Field K] [Fintype K] [CommRing A] [Algebra K A] :
    Submodule K A :=
  ((FiniteField.frobeniusAlgHom K A).toLinearMap - LinearMap.id).ker

theorem mem_fixedSpace (x : A) : x ∈ fixedSpace K A ↔ x ^ Fintype.card K = x := by
  change ((FiniteField.frobeniusAlgHom K A) x - x = 0) ↔ _
  exact sub_eq_zero

/-- A list spanning the fixed space, in actual algebra coordinates. -/
def rawFixed (C : A ≃ₗ[K] (Fin d → K)) : List A :=
  (rawKernelVectors (LinearMap.toMatrix' (fixedDifference C)) (Equiv.refl _) (Equiv.refl _)).map
    C.symm

theorem rawFixed_span (C : A ≃ₗ[K] (Fin d → K)) :
    Submodule.span K {x | x ∈ rawFixed C} = fixedSpace K A := by
  let M := LinearMap.toMatrix' (fixedDifference C)
  let xs := rawKernelVectors M (Equiv.refl _) (Equiv.refl _)
  have hx :
      Submodule.span K {x | x ∈ xs} = M.mulVecLin.ker := by
    have hset : {x | x ∈ xs} = Set.range xs.get := by
      ext x
      exact List.mem_iff_get
    rw [hset]
    exact rawKernelVectors_span M _ _
  have hs : {x | x ∈ rawFixed C} = C.symm.toLinearMap '' {x | x ∈ xs} := by
    ext x
    exact List.mem_map
  rw [hs, ← Submodule.map_span, hx]
  change Submodule.map C.symm.toLinearMap
    (LinearMap.toMatrix' (fixedDifference C)).mulVecLin.ker = _
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  ext x
  change (∃ y ∈ (fixedDifference C).ker, C.symm y = x) ↔ x ∈ fixedSpace K A
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply LinearMap.mem_ker.mpr
    exact C.injective ((LinearMap.mem_ker.mp hy).trans (C.map_zero).symm)
  · intro hx
    refine ⟨C x, LinearMap.mem_ker.mpr ?_, C.symm_apply_apply x⟩
    let D : A →ₗ[K] A := (FiniteField.frobeniusAlgHom K A).toLinearMap - LinearMap.id
    change C (D (C.symm (C x))) = 0
    have hz : D x = 0 := LinearMap.mem_ker.mp hx
    rw [C.symm_apply_apply, hz, C.map_zero]

theorem rawFixed_mem (C : A ≃ₗ[K] (Fin d → K)) {x : A} (hx : x ∈ rawFixed C) :
    x ^ Fintype.card K = x := by
  apply (mem_fixedSpace (K := K) x).mp
  rw [← rawFixed_span C]
  exact Submodule.subset_span hx

theorem rawFixed_length_le (C : A ≃ₗ[K] (Fin d → K)) : (rawFixed C).length ≤ d := by
  rw [rawFixed, List.length_map]
  exact rawKernelVectors_length_le (LinearMap.toMatrix' (fixedDifference C)) _ _

#print axioms rawFixed_span
#print axioms rawFixed_length_le

end EvenTI.CellProducer
