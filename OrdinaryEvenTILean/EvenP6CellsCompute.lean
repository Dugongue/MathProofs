import EvenP6CellsFixed
import EvenP6CellsFrame

/-! An executable field-cell decomposition over a finite base field.
Frobenius-fixed coordinates and the scalar projectors are computed from
the represented algebra and its checked coordinate basis. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped BigOperators
open Module

variable {K A : Type} [Field K] [Fintype K] [DecidableEq K]
  [CommRing A] [Algebra K A] [DecidableEq A] {d : ℕ}

/-- Each returned element is the unit of one field cell. -/
def rawCells (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K)) : List A :=
  if (1 : A) = 0 then [] else run enum (rawFixed C) [1]

theorem rawCells_partition
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K)) :
    IsPartition (rawCells enum C) := by
  by_cases h : (1 : A) = 0
  · simp [rawCells, h, IsPartition]
  · rw [rawCells, if_neg h]
    exact run_partition enum (rawFixed C) (fun _ hb => rawFixed_mem C hb)
      (by simp [IsPartition, h])

private def scalarActors (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (es : List A) : Submodule K A where
  carrier := {x | ActsScalar (K := K) x es}
  zero_mem' := by
    intro e he
    exact ⟨0, by simp⟩
  add_mem' := by
    intro x y hx hy e he
    obtain ⟨a, ha⟩ := hx e he
    obtain ⟨b, hb⟩ := hy e he
    exact ⟨a + b, by rw [add_mul, ha, hb, map_add, add_mul]⟩
  smul_mem' := by
    intro c x hx e he
    obtain ⟨a, ha⟩ := hx e he
    exact ⟨c * a, by rw [smul_mul_assoc, ha, map_mul, Algebra.smul_def, mul_assoc]⟩

theorem rawCells_acts_scalar
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (x : A) (hx : x ^ Fintype.card K = x) : ActsScalar (K := K) x (rawCells enum C) := by
  by_cases h₀ : (1 : A) = 0
  · simp [rawCells, h₀, ActsScalar]
  rw [rawCells, if_neg h₀]
  have h : fixedSpace K A ≤ scalarActors K A (run enum (rawFixed C) [1]) := by
    rw [← rawFixed_span C]
    apply Submodule.span_le.mpr
    exact run_acts_scalar enum (rawFixed C) (fun _ h => rawFixed_mem C h) (by simp [IsPartition, h₀])
  exact h ((mem_fixedSpace x).mpr hx)

theorem rawCells_length_le [FiniteDimensional K A]
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K)) :
    (rawCells enum C).length ≤ d := by
  have h := partition_length_le (K := K) (rawCells_partition enum C)
  rw [C.finrank_eq] at h
  simpa using h

section Transport

variable {J : Type} [Fintype J] {F : J → Type}
  [∀ j, Field (F j)] [∀ j, Algebra K (F j)]

private theorem image_cell_is_single [DecidableEq J]
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) {e : A} (he : e ∈ rawCells enum C) :
    ∃ j : J, E e = Pi.single j 1 := by
  obtain ⟨hne, hidem⟩ := (rawCells_partition enum C).1 e he
  have heCoeff (j : J) : E e j = 0 ∨ E e j = 1 := by
    have h := congrArg (fun a => E a j) hidem
    simp only [map_mul, Pi.mul_apply] at h
    rcases mul_eq_zero.mp (show E e j * (E e j - 1) = 0 by rw [mul_sub, mul_one, h, sub_self])
      with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h1)
  obtain ⟨j, hj⟩ : ∃ j, E e j ≠ 0 := by
    by_contra! h
    apply hne
    apply E.injective
    funext j
    rw [h j, map_zero]
    rfl
  have h1 := (heCoeff j).resolve_left hj
  let t : A := E.symm (Pi.single j 1)
  have ht : t ^ Fintype.card K = t := by
    apply E.injective
    rw [map_pow, AlgEquiv.apply_symm_apply]
    funext k
    by_cases h : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne h, Nat.ne_of_gt (Fintype.card_pos (α := K))]
  obtain ⟨a, ha⟩ := rawCells_acts_scalar enum C t ht e he
  have hc (k : J) : Pi.single j (1 : F j) k * E e k = algebraMap K (F k) a * E e k := by
    have h := congrArg (fun u => E u k) ha
    simpa only [map_mul, Pi.mul_apply, t, AlgEquiv.apply_symm_apply, AlgEquiv.commutes,
      Pi.algebraMap_apply] using h
  have ha1 : a = 1 := by
    apply (algebraMap K (F j)).injective
    simpa [h1, eq_comm] using hc j
  refine ⟨j, ?_⟩
  funext k
  by_cases h : k = j
  · subst k
    simp [h1]
  · simpa [Pi.single_eq_of_ne h, ha1, eq_comm] using hc k

/-- The actual field-cell list is precisely the singleton-coordinate frame
of any splitting equivalence, up to the produced list order. -/
theorem rawCells_exact [DecidableEq J]
    (enum : Fin (Fintype.card K) ≃ K) (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) :
    ∃ order : Fin (rawCells enum C).length ≃ J,
      ∀ i, E ((rawCells enum C).get i) = Pi.single (order i) 1 := by
  classical
  let es := rawCells enum C
  have hpart := rawCells_partition enum C
  obtain ⟨p, hp⟩ : ∃ p : Fin es.length → J, ∀ i,
      E (es.get i) = Pi.single (p i) 1 := by
    choose p hp using (fun i : Fin es.length =>
      image_cell_is_single enum C E (es.get_mem i))
    exact ⟨p, hp⟩
  have hinj : Function.Injective p := by
    intro i j hij
    by_contra hn
    have he : es.get i = es.get j := E.injective (by rw [hp i, hp j, hij])
    have hz := get_orthogonal hpart i j hn
    rw [← he, (hpart.1 _ (es.get_mem i)).2] at hz
    exact (hpart.1 _ (es.get_mem i)).1 hz
  have hsurj : Function.Surjective p := by
    intro j
    by_contra! h
    have hsum : (∑ i : Fin es.length, es.get i) = 1 := by
      change (∑ i : Fin es.length, es[i.val]) = 1
      rw [Fin.sum_univ_getElem]
      exact hpart.2.2
    have hc := congrArg (fun z => E z j) hsum
    simp only [map_sum, Finset.sum_apply, map_one, Pi.one_apply] at hc
    have hz : (∑ i : Fin es.length, E (es.get i) j) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hp]
      exact Pi.single_eq_of_ne (Ne.symm (h i)) _
    exact zero_ne_one (hz.symm.trans hc)
  exact ⟨Equiv.ofBijective p ⟨hinj, hsurj⟩, hp⟩

end Transport

#print axioms rawCells_exact
#print axioms rawCells_length_le

end EvenTI.CellProducer
