import EvenP6CellsCoordinates
import EvenP6CellsLinearSolve

/-! Compute the ratio of a target and a nonzero source in the given live
field corner. The augmented base-field solve never enumerates the corner. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace EvenTI.CellProducer

open scoped BigOperators
open EvenTI.CellLinearSolve

variable {K A : Type} [Field K] [DecidableEq K] [CommRing A] [Algebra K A] {d : ℕ}

private def basisWord (j : Fin d) : Fin d → K := Pi.single j 1

private theorem sum_basisWord (w : Fin d → K) :
    ∑ j, w j • basisWord j = w := by
  simpa only [basisWord, Pi.basisFun_apply, Pi.basisFun_repr] using
    (Pi.basisFun K (Fin d)).sum_repr w

/-- Compute a ratio in the given field corner using a base-field linear solve. -/
def rawCellDivision (C : A ≃ₗ[K] (Fin d → K)) (e source target : A) : Option A :=
  (solveStored (List.finRange d) (fun j => cornerCoordMap C (e * source) (basisWord j))
    (C (e * target))).map fun w => e * C.symm w

theorem rawCellDivision_sound (C : A ≃ₗ[K] (Fin d → K)) {e source target r : A}
    (he : e * e = e) (h : rawCellDivision C e source target = some r) :
    e * r = r ∧ (e * source) * r = e * target := by
  unfold rawCellDivision at h
  obtain ⟨w, hw, rfl⟩ := Option.map_eq_some_iff.mp h
  let L := cornerCoordMap C (e * source)
  have hrep := solveStored_correct List.mem_finRange (fun j => L (basisWord j)) _ _ hw
  have hL : L w = C (e * target) := calc
    _ = L (∑ j, w j • basisWord j) := by rw [sum_basisWord]
    _ = _ := by simpa only [map_sum, map_smul] using hrep
  have hmul : (e * source) * C.symm w = e * target := C.injective hL
  refine ⟨by rw [← mul_assoc, he], ?_⟩
  rw [← mul_assoc, show e * source * e = e * source by rw [mul_comm (e * source) e, ← mul_assoc, he]]
  exact hmul

theorem rawCellDivision_isSome (C : A ≃ₗ[K] (Fin d → K)) (e source target : A)
    (h : ∃ w : A, (e * source) * w = e * target) :
    (rawCellDivision C e source target).isSome := by
  obtain ⟨w, hw⟩ := h
  let L := cornerCoordMap C (e * source)
  have hr : C (e * target) ∈ Submodule.span K (Set.range fun j => L (basisWord j)) := by
    apply (Submodule.mem_span_range_iff_exists_fun K).mpr
    refine ⟨C w, ?_⟩
    simp_rw [← L.map_smul, ← map_sum]
    change L (∑ j, C w j • basisWord j) = _
    rw [sum_basisWord]
    change C ((e * source) * C.symm (C w)) = _
    rw [C.symm_apply_apply, hw]
  have hs := solveStored_total (List.finRange d) List.mem_finRange
    (fun j => L (basisWord j)) _ hr
  simpa only [rawCellDivision, Option.isSome_map] using hs

section Splitting

variable {J : Type} {F : J → Type} [∀ j, Field (F j)] [∀ j, Algebra K (F j)]
  [DecidableEq J]

/-- Projecting two ambient inputs and solving in the actual corner computes
the field ratio prescribed by the splitting equivalence. -/
theorem rawCellDivision_exact (C : A ≃ₗ[K] (Fin d → K))
    (E : A ≃ₐ[K] (∀ j, F j)) (j : J) {e source target : A}
    (he : E e = Pi.single j 1) (hs : E source j ≠ 0) :
    ∃ r : A, rawCellDivision C e source target = some r ∧
      E r = Pi.single j (E target j / E source j) := by
  have hIdem : e * e = e := by
    apply E.injective
    rw [map_mul, he]
    funext t
    by_cases h : t = j
    · subst t; simp
    · simp [Pi.single_eq_of_ne h]
  let w := E.symm (Pi.single j (E target j / E source j))
  have hw : (e * source) * w = e * target := by
    apply E.injective
    simp only [map_mul, he, w, AlgEquiv.apply_symm_apply]
    funext t
    by_cases h : t = j
    · subst t
      simp only [Pi.mul_apply, Pi.single_eq_same, one_mul]
      rw [mul_comm, div_mul_cancel₀ _ hs]
    · simp [Pi.single_eq_of_ne h]
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
    (rawCellDivision_isSome C e source target ⟨w, hw⟩)
  have hRun := rawCellDivision_sound C hIdem hr
  refine ⟨r, hr, ?_⟩
  funext t
  by_cases h : t = j
  · subst t
    have hj := congrArg (fun z => E z j) hRun.2
    simp only [map_mul, Pi.mul_apply, he, Pi.single_eq_same, one_mul] at hj
    rw [Pi.single_eq_same, eq_div_iff hs, mul_comm]
    exact hj
  · have ht := congrArg (fun z => E z t) hRun.1
    simp only [map_mul, Pi.mul_apply, he, Pi.single_eq_of_ne h, zero_mul] at ht
    simpa only [Pi.single_eq_of_ne h] using ht.symm

end Splitting

#print axioms rawCellDivision_sound
#print axioms rawCellDivision_exact

end EvenTI.CellProducer
