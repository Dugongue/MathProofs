import EvenP3SingularRectAlgebra
import EvenP2PolarTarget

namespace Mathproof.EvenOrdinaryTISingular.RectPolar

open LinearMap Matrix PolarOperator EvenTI.Primary
open Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget
noncomputable section

variable {K : Type*} [Field K] {u v : ℕ}

def leftCoordinate : jointTarget K u v →ₗ[K] M K u :=
  (LinearMap.fst K _ _).comp (jointTarget K u v).subtype

def rightCoordinate : jointTarget K u v →ₗ[K] M K v :=
  (LinearMap.snd K _ _).comp (jointTarget K u v).subtype

private theorem mem_odd {X : M K u} {Y : M K v}
    (h₂ : (2 : K) ≠ 0) (h : X.trace = Y.trace) : (X,Y) ∈ jointTarget K u v := by
  unfold jointTarget
  rw [if_neg h₂]
  exact sub_eq_zero.mpr h

private theorem mem_two {X : M K u} {Y : M K v}
    (h₂ : (2 : K) = 0) :
    (X,Y) ∈ jointTarget K u v ↔ X.trace = 0 ∧ Y.trace = 0 := by
  unfold jointTarget
  rw [if_pos h₂]
  rfl

theorem leftCoordinate_surjective (h₂ : (2 : K) ≠ 0) (hv : 0 < v) :
    Function.Surjective (leftCoordinate (K := K) (u := u) (v := v)) := by
  letI : Nonempty (Fin v) := ⟨⟨0,hv⟩⟩
  intro X
  obtain ⟨Y, hY⟩ := Matrix.trace_surjective (n := Fin v) X.trace
  exact ⟨⟨(X,Y), mem_odd h₂ hY.symm⟩, rfl⟩

theorem rightCoordinate_surjective (h₂ : (2 : K) ≠ 0) (hu : 0 < u) :
    Function.Surjective (rightCoordinate (K := K) (u := u) (v := v)) := by
  letI : Nonempty (Fin u) := ⟨⟨0,hu⟩⟩
  intro Y
  obtain ⟨X, hX⟩ := Matrix.trace_surjective (n := Fin u) Y.trace
  exact ⟨⟨(X,Y), mem_odd h₂ hX⟩, rfl⟩

def leftCoordinateZero (h₂ : (2 : K) = 0) :
    jointTarget K u v →ₗ[K] TraceZero K (Fin u) :=
  leftCoordinate.codRestrict _ (fun Z => ((mem_two h₂).mp Z.property).1)

def rightCoordinateZero (h₂ : (2 : K) = 0) :
    jointTarget K u v →ₗ[K] TraceZero K (Fin v) :=
  rightCoordinate.codRestrict _ (fun Z => ((mem_two h₂).mp Z.property).2)

theorem leftCoordinateZero_surjective (h₂ : (2 : K) = 0) :
    Function.Surjective (leftCoordinateZero (K := K) (u := u) (v := v) h₂) := by
  intro X
  exact ⟨⟨(X.val,0),(mem_two h₂).mpr ⟨X.property,by simp⟩⟩, Subtype.ext rfl⟩

theorem rightCoordinateZero_surjective (h₂ : (2 : K) = 0) :
    Function.Surjective (rightCoordinateZero (K := K) (u := u) (v := v) h₂) := by
  intro Y
  exact ⟨⟨(0,Y.val),(mem_two h₂).mpr ⟨by simp,Y.property⟩⟩, Subtype.ext rfl⟩

variable [Fintype K]

local instance : Fintype (jointTarget K u v) := Fintype.ofFinite _
local instance {n : ℕ} : Fintype (TraceZero K (Fin n)) := Fintype.ofFinite _

private theorem mean_independent_fintype {A : Type*} (F G : Fintype A) (f : A → ℝ) :
    @mean A F f = @mean A G f := by
  obtain rfl := Subsingleton.elim F G
  rfl

theorem mean_left_primary_budget_le (hu : 0 < u) (hv : 0 < v) :
    mean (fun x : jointTarget K u v => (repeatedBudget (leftCoordinate x).charpoly : ℝ)) ≤
      budgetConstant K := by
  by_cases h₂ : (2 : K) = 0
  · let f (x : TraceZero K (Fin u)) := (repeatedBudget x.val.charpoly : ℝ)
    change mean (f ∘ leftCoordinateZero h₂) ≤ _
    rw [mean_comp_eq_uniform_linear _ (leftCoordinateZero_surjective h₂)]
    exact (mean_independent_fintype _ _ f).le.trans (mean_trace_budget_le u hu (0 : K))
  · let f (x : M K u) := (repeatedBudget x.charpoly : ℝ)
    change mean (f ∘ leftCoordinate) ≤ _
    rw [mean_comp_eq_uniform_linear _ (leftCoordinate_surjective h₂ hv)]
    exact mean_matrix_budget_le (K := K) u

theorem mean_right_primary_budget_le (hu : 0 < u) (hv : 0 < v) :
    mean (fun x : jointTarget K u v => (repeatedBudget (rightCoordinate x).charpoly : ℝ)) ≤
      budgetConstant K := by
  by_cases h₂ : (2 : K) = 0
  · let f (x : TraceZero K (Fin v)) := (repeatedBudget x.val.charpoly : ℝ)
    change mean (f ∘ rightCoordinateZero h₂) ≤ _
    rw [mean_comp_eq_uniform_linear _ (rightCoordinateZero_surjective h₂)]
    exact (mean_independent_fintype _ _ f).le.trans (mean_trace_budget_le v hv (0 : K))
  · let f (x : M K v) := (repeatedBudget x.charpoly : ℝ)
    change mean (f ∘ rightCoordinate) ≤ _
    rw [mean_comp_eq_uniform_linear _ (rightCoordinate_surjective h₂ hu)]
    exact mean_matrix_budget_le (K := K) v

end
end Mathproof.EvenOrdinaryTISingular.RectPolar

#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.mean_left_primary_budget_le
#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.mean_right_primary_budget_le
