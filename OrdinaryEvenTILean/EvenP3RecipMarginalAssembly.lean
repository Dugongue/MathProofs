import EvenP3RecipSlicedAnchor
import EvenP1Coverage

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Primary Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K H L J I B : Type*} [Field K] [Fintype K] [Nonempty I]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "Shear" => UpperShear K H L (Option J)
local notation "TraceZero" => traceKernel (K := K) (I := I)
local notation "Full" => (⊤ : Submodule K (Matrix I I K))
local notation "Target" => AnchorTrace K (Sum H L × Option J) I

def slicedBad (s : ℕ) (A : Bases) : Prop :=
  ∃ P : Matrix I I K,
    (restrictedMatrixLabelRank P ≤ s ∧ physicalMatrixLabelRank A P < 15 * restrictedMatrixLabelRank P) ∨
    (s < restrictedMatrixLabelRank P ∧ physicalMatrixLabelRank A P < 4*(Fintype.card I)^2)

abbrev slicedShearError (K I : Type*) [Fintype K] [Fintype I] (s : ℕ) : ℝ :=
  Real.sqrt ((↑(s+1) : ℝ) * ((Fintype.card K : ℝ)^(9*Fintype.card I-31))⁻¹ +
    (Fintype.card K : ℝ)^(Fintype.card I^2) * ((Fintype.card K : ℝ)^(4*Fintype.card I^2))⁻¹)

private theorem nontrivial_field_character : ∃ ψ : AddChar K ℂ, ψ ≠ 1 := by
  have : Nontrivial (AddChar K ℂ) := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [AddChar.card_eq]
    exact Fintype.one_lt_card)
  exact exists_ne 1

private theorem l1_of_good_sliced (A : Bases) (hn : 4 ≤ Fintype.card I)
    (S : Submodule K (Matrix I I K)) [Fintype S] [Fintype (Module.Dual K S)]
    (hS : ∀ X : Shear, Small.anchor (applyShear X A) - Small.anchor A ∈ S)
    (s : ℕ) (hA : ¬ slicedBad s A)
    (hMin : ∀ c : Module.Dual K S, c ≠ 0 → Fintype.card I-2 ≤ restrictedMatrixLabelRank (matrixLabelChoice S c)) :
    marginalError (fun X : Shear => (⟨Small.anchor (applyShear X A) - Small.anchor A, hS X⟩ : S)) ≤
      slicedShearError K I s := by
  obtain ⟨ψ, hψ⟩ := nontrivial_field_character (K := K)
  apply square_reciprocal_shear_l1_of_good_label_ranks A hn S hS ψ hψ s hMin
  · exact fun P hp => Nat.le_of_not_gt (fun h => hA ⟨P, Or.inl ⟨hp,h⟩⟩)
  · exact fun P hp => Nat.le_of_not_gt (fun h => hA ⟨P, Or.inr ⟨hp,h⟩⟩)

theorem square_trace_marginal_of_sliced_bad_mass [CharP K 2] [Fintype Bases] [Nonempty Bases]
    [Fintype TraceZero] [Fintype Target] (hn : 4 ≤ Fintype.card I) (s : ℕ) :
    marginalError (traceAnchor : Bases → Target) ≤
      slicedShearError K I s + 2 * event (slicedBad s : Bases → Prop) := by
  rw [show (slicedBad s : Bases → Prop) = (fun A => ¬ ¬ slicedBad s A) from
    funext (fun _ => (propext not_not).symm)]
  apply marginalError_of_good_baselines (fun X => shearEquiv X) traceAnchor
    (fun A => ¬ slicedBad s A) _ (Real.sqrt_nonneg _)
  intro A hA
  letI : Fintype (Module.Dual K TraceZero) := Fintype.ofInjective
    (fun f : Module.Dual K TraceZero => (f : TraceZero → K)) DFunLike.coe_injective
  let f : Shear → TraceZero :=
    fun X => ⟨Small.anchor (applyShear X A) - Small.anchor A, anchor_difference_mem_traceKernel A X⟩
  have he : (fun X => traceAnchor (shearEquiv X A)) = traceTranslate A ∘ f := by
    funext X
    exact Subtype.ext (sub_add_cancel _ _).symm
  rw [he, marginalError_equiv]
  apply l1_of_good_sliced A hn TraceZero (anchor_difference_mem_traceKernel A) s hA
  intro c hc
  apply traceZero_label_rank
  rwa [matrixLabelChoice_spec]

theorem square_odd_marginal_of_sliced_bad_mass [Fintype Bases] [Nonempty Bases] [Fintype Full]
    (hn : 4 ≤ Fintype.card I) (s : ℕ) (h₂ : (2 : K) ≠ 0) :
    marginalError (Small.anchor : Bases → Matrix I I K) ≤
      slicedShearError K I s + 2 * event (slicedBad s : Bases → Prop) := by
  rw [show (slicedBad s : Bases → Prop) = (fun A => ¬ ¬ slicedBad s A) from
    funext (fun _ => (propext not_not).symm)]
  apply marginalError_of_good_baselines (fun X => shearEquiv X) Small.anchor
    (fun A => ¬ slicedBad s A) _ (Real.sqrt_nonneg _)
  intro A hA
  letI : Fintype (Module.Dual K Full) := Fintype.ofInjective
    (fun f : Module.Dual K Full => (f : Full → K)) DFunLike.coe_injective
  let f : Shear → Full :=
    fun X => ⟨Small.anchor (applyShear X A) - Small.anchor A, Submodule.mem_top⟩
  have he : (fun X => Small.anchor (shearEquiv X A)) = fullTranslate A ∘ f := by
    funext X
    exact (sub_add_cancel _ _).symm
  rw [he, marginalError_equiv]
  apply l1_of_good_sliced A hn Full (fun _ => Submodule.mem_top) s hA
  intro c hc
  apply traceZero_odd_label_rank _ _ h₂
  intro h
  apply hc
  rw [← matrixLabelChoice_spec Full c, h]
  simp

#print axioms square_trace_marginal_of_sliced_bad_mass
#print axioms square_odd_marginal_of_sliced_bad_mass

end
end Mathproof.EvenTI.Reciprocal.Coverage
