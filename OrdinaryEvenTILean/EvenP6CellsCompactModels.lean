import EvenP6CellsCompact
import Mathlib.RingTheory.Artinian.Module

/-! The semantic splitting is used only in proof fields. Every generated
cell of a finite reduced input receives the executable Field instance. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped BigOperators
open Module

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] [DecidableEq A] {d : ℕ}

theorem rawCell_field_of_reduced [IsReduced A]
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (i : Fin (rawCells enum C).length) :
    CellFieldCertificate C ((rawCells enum C).get i) := by
  classical
  letI : Module.Finite K A := Module.Finite.of_basis (Basis.ofEquivFun C)
  letI : IsArtinianRing A := IsArtinianRing.of_finite K _
  letI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _
  letI (j : MaximalSpectrum A) : Field (A ⧸ j.asIdeal) :=
    IsArtinianRing.fieldOfSubtypeIsMaximal A j
  exact rawCell_field_certificate (J := MaximalSpectrum A) (F := fun j => A ⧸ j.asIdeal)
    enum C ((IsArtinianRing.equivPi A).restrictScalars K) i

section Model

variable {J : Type} [DecidableEq J]
  {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

/-- Equality of all corner operations with the corresponding true field. -/
noncomputable def compactModelEquiv (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) (j : J) (e : A)
    (he : E e = Pi.single j 1) [h : CellFieldCertificate C e] :
    CompactCell C e ≃ₐ[K] F j where
  toEquiv := (TableWord.wordEquiv _).trans (cellWordEquiv C E j he).toEquiv
  map_mul' x y := by
    change E (cellDecoder C e (x * y).val) j =
      E (cellDecoder C e x.val) j * E (cellDecoder C e y.val) j
    rw [TableWord.val_mul, cellDecoder_mul C e h.idem, map_mul, Pi.mul_apply]
  map_add' x y := by
    change E (cellDecoder C e (x.val + y.val)) j =
      E (cellDecoder C e x.val) j + E (cellDecoder C e y.val) j
    rw [map_add, map_add, Pi.add_apply]
  commutes' k := by
    change E (cellDecoder C e (k • (compactTable C e).one)) j = algebraMap K (F j) k
    rw [map_smul, cellDecoder_one C e h.idem, map_smul]
    change ((k • E e) j) = _
    rw [he, Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, mul_one]

end Model

#print axioms rawCell_field_of_reduced
#print axioms compactModelEquiv

end EvenTI.CellProducer
