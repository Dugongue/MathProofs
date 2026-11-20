import EvenP6CellsCoordinates
import EvenP6CellsCompute
import EvenP6CellsRatio
import Mathlib.FieldTheory.Finite.Basic

/-! Bind the actual field-cell vectors and arithmetic to the abstract
field factors, including their exact extension degrees. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open Module
open scoped BigOperators

variable {K A : Type} [Field K] [DecidableEq K] [CommRing A] [Algebra K A] {d : ℕ}
  {J : Type} [DecidableEq J] {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

theorem project_to_field (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e : A}
    (he : E e = Pi.single j 1) (x : A) :
    E (e * x) = Pi.single j (E x j) := by
  rw [map_mul, he]
  funext k
  by_cases h : k = j
  · subst k; simp
  · simp [Pi.single_eq_of_ne h]

theorem idempotent_of_field_projection (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e : A}
    (he : E e = Pi.single j 1) : e * e = e := by
  apply E.injective
  rw [project_to_field E j he, he]
  simp

theorem cellDecode_algebraMap {B : Type} [Semiring B] [Algebra K B]
    (C : A ≃ₗ[K] (Fin d → K)) (E : A ≃ₐ[K] (∀ j, F j)) (j : J)
    {e : A} (he : E e = Pi.single j 1) (f : B →ₐ[K] A) (x : B) :
    E (cellDecode C e (cellEmbedding C e f x)) = Pi.single j (E (f x) j) := by
  rw [cellDecode_embedding, project_to_field E j he]

/-- Evaluating compact corner words is a linear bijection onto the actual
field coordinate. Only this semantic bijection uses classical choice. -/
noncomputable def cellWordEquiv (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e : A} (he : E e = Pi.single j 1) :
    (Fin (rawCellDegree C e) → K) ≃ₗ[K] F j := by
  let φ : (Fin (rawCellDegree C e) → K) →ₗ[K] A :=
    C.symm.toLinearMap.comp (Fintype.linearCombination K (fun i => ((rawCellRows C e).get i).2))
  let γ : (Fin (rawCellDegree C e) → K) →ₗ[K] F j :=
    (LinearMap.proj j).comp (E.toLinearMap.comp φ)
  have hApply (v : Fin (rawCellDegree C e) → K) : γ v = E (cellDecode C e v) j := rfl
  have hIdem := idempotent_of_field_projection E j he
  have hSupport (v : Fin (rawCellDegree C e) → K) :
      E (cellDecode C e v) = Pi.single j (γ v) := by
    rw [← cellDecode_fixed C hIdem v, project_to_field E j he, hApply]
  refine LinearEquiv.ofBijective γ ⟨?_, ?_⟩
  · intro x y h
    have hEq : cellDecode C e x = cellDecode C e y := E.injective (by
      rw [hSupport x, hSupport y, h])
    rw [← cellCoefficients_decode C hIdem x, hEq, cellCoefficients_decode C hIdem y]
  · intro a
    let u := E.symm (Pi.single j a)
    refine ⟨cellCoefficients C e u, ?_⟩
    rw [hApply, cellDecode_coefficients, project_to_field E j he]
    simp [u]

theorem rawCellDegree_eq_field_finrank (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e : A} (he : E e = Pi.single j 1) :
    rawCellDegree C e = finrank K (F j) := by
  simpa using (cellWordEquiv C E j he).finrank_eq

section Complete

variable [Fintype K] [DecidableEq A] [Fintype J] [∀ j, Module.Finite K (F j)]

theorem rawCells_sum_degrees (enum : Fin (Fintype.card K) ≃ K)
    (C : A ≃ₗ[K] (Fin d → K)) (E : A ≃ₐ[K] (∀ j, F j)) :
    (∑ i : Fin (rawCells enum C).length, rawCellDegree C ((rawCells enum C).get i)) = d := by
  obtain ⟨p, hp⟩ := rawCells_exact enum C E
  simp_rw [rawCellDegree_eq_field_finrank C E _ (hp _)]
  rw [Equiv.sum_comp p (fun j => finrank K (F j)), ← Module.finrank_pi_fintype K,
    ← E.toLinearEquiv.finrank_eq, C.finrank_eq]
  simp

end Complete

#print axioms cellDecode_algebraMap
#print axioms rawCellDegree_eq_field_finrank
#print axioms rawCells_sum_degrees

end EvenTI.CellProducer
