import EvenP2PolarOperators
import EvenPrimaryMarginal
import EvenPrimaryMoment
import EvenLiveSingularBlock

namespace Mathproof.EvenOrdinaryTISingular

open scoped BigOperators Classical
open Matrix Module LinearMap PolarOperator EvenTI.Primary
open Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget

noncomputable section

/-- A uniform sample pushed through a surjective linear map has the target
uniform mean for every real-valued test. -/
theorem mean_comp_eq_uniform_linear {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype V] [AddCommGroup W] [Module K W] [Fintype W]
    (g : V →ₗ[K] W) (hg : Function.Surjective g) (f : W → ℝ) :
    mean (f ∘ g) = mean f := by
  classical
  have hw (y : W) : weight g y = (Fintype.card W : ℝ)⁻¹ := by
    rw [weight, event_eq_card]
    have h := uniformFraction_linear_surjective g hg (fun x => x = y)
    unfold uniformFraction at h
    rw [Nat.card_eq_fintype_card (α := {x : W // x = y}), Fintype.card_subtype_eq,
      Nat.cast_one, Nat.card_eq_fintype_card (α := W), one_div] at h
    exact h
  rw [mean_comp_eq_weight]
  simp only [hw, ← Finset.sum_mul, mean, div_eq_mul_inv]

variable {K : Type*} [Field K] {n : ℕ}

def jointCoordinate (right : Bool) : jointTarget K n →ₗ[K] M K n :=
  (if right then LinearMap.snd K (M K n) (M K n) else LinearMap.fst K (M K n) (M K n)).comp
    (jointTarget K n).subtype

theorem jointCoordinate_false (x : jointTarget K n) :
    jointCoordinate false x = x.val.1 := rfl

theorem jointCoordinate_true (x : jointTarget K n) :
    jointCoordinate true x = x.val.2 := rfl

private theorem joint_diag_mem (A : M K n) (h : (2 : K) ≠ 0 ∨ A.trace = 0) :
    (A, A) ∈ jointTarget K n := by
  unfold jointTarget
  split_ifs with h₂
  · change A.trace = 0 ∧ A.trace = 0
    have hz := h.resolve_left (not_not_intro h₂)
    exact ⟨hz, hz⟩
  · change A.trace - A.trace = 0
    exact sub_self _

theorem jointCoordinate_surjective (h₂ : (2 : K) ≠ 0) (right : Bool) :
    Function.Surjective (jointCoordinate (K := K) (n := n) right) := by
  intro A
  refine ⟨⟨(A,A), joint_diag_mem A (Or.inl h₂)⟩, ?_⟩
  cases right <;> rfl

private theorem jointCoordinate_mem_traceZero (h₂ : (2 : K) = 0) (right : Bool)
    (x : jointTarget K n) : jointCoordinate right x ∈ TraceZero K (Fin n) := by
  have ht : jointTarget K n = (leftTrace K n).ker ⊓ (rightTrace K n).ker := by
    unfold jointTarget
    rw [if_pos h₂]
  have h : x.val ∈ (leftTrace K n).ker ⊓ (rightTrace K n).ker :=
    Eq.mp (congrArg (fun W : Submodule K (M K n × M K n) => x.val ∈ W) ht) x.property

  change x.val.1.trace = 0 ∧ x.val.2.trace = 0 at h
  cases right
  · exact h.1
  · exact h.2

def jointCoordinateZero (h₂ : (2 : K) = 0) (right : Bool) :
    jointTarget K n →ₗ[K] TraceZero K (Fin n) :=
  (jointCoordinate right).codRestrict _ (jointCoordinate_mem_traceZero h₂ right)

theorem jointCoordinateZero_surjective (h₂ : (2 : K) = 0) (right : Bool) :
    Function.Surjective (jointCoordinateZero (K := K) (n := n) h₂ right) := by
  intro A
  refine ⟨⟨(A.val,A.val), joint_diag_mem A.val (Or.inr A.property)⟩, ?_⟩
  apply Subtype.ext
  cases right <;> rfl

variable [Fintype K]

local instance : Fintype (jointTarget K n) := Fintype.ofFinite _
local instance : Fintype (TraceZero K (Fin n)) := Fintype.ofFinite _

theorem mean_joint_coordinate_odd (h₂ : (2 : K) ≠ 0) (right : Bool) (f : M K n → ℝ) :
    mean (f ∘ jointCoordinate right) = mean f :=
  mean_comp_eq_uniform_linear _ (jointCoordinate_surjective h₂ right) f

theorem mean_joint_coordinate_charTwo (h₂ : (2 : K) = 0) (right : Bool)
    (f : TraceZero K (Fin n) → ℝ) :
    mean (f ∘ jointCoordinateZero h₂ right) = mean f :=
  mean_comp_eq_uniform_linear _ (jointCoordinateZero_surjective h₂ right) f

private theorem mean_independent_fintype {A : Type*} (F G : Fintype A) (f : A → ℝ) :
    @mean A F f = @mean A G f := by
  obtain rfl := Subsingleton.elim F G
  rfl

/-- In either characteristic, either coordinate of the uniform target
has the existing field-dependent primary-budget expectation bound. -/
theorem mean_joint_primary_budget_le (hn : 0 < n) (right : Bool) :
    mean (fun x : jointTarget K n => (repeatedBudget (jointCoordinate right x).charpoly : ℝ)) ≤
      budgetConstant K := by
  by_cases h₂ : (2 : K) = 0
  · let f : TraceZero K (Fin n) → ℝ := fun x => (repeatedBudget x.val.charpoly : ℝ)
    change mean (f ∘ jointCoordinateZero h₂ right) ≤ _
    rw [mean_joint_coordinate_charTwo]
    exact (mean_independent_fintype _ _ f).le.trans (mean_trace_budget_le n hn (0 : K))
  · let f : M K n → ℝ := fun x => (repeatedBudget x.charpoly : ℝ)
    change mean (f ∘ jointCoordinate right) ≤ _
    rw [mean_joint_coordinate_odd h₂]
    exact mean_matrix_budget_le (K := K) n

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.mean_joint_coordinate_odd
#print axioms Mathproof.EvenOrdinaryTISingular.mean_joint_coordinate_charTwo
#print axioms Mathproof.EvenOrdinaryTISingular.mean_joint_primary_budget_le


