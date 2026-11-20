import EvenP1Coverage
import EvenP2SpectralBasic

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical Matrix
open Matrix EvenTI.Action EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.Problem17PrimaryTail Mathproof.Problem17RepeatedBudget
open Mathproof.EvenTI.Singular.Coverage
  (event_as_fraction primary_pointwise_cap spectral_gate_of_mode_means square_mul_field_decay)

noncomputable section

abbrev HigherModes (l : ℕ) := Bool × Fin (l + 1)

variable {K : Type} [Field K] [Fintype K] {l n : ℕ}

/-- The anchor in the physical mode named by a cut orientation and a mode
in the right half of that orientation. -/
def higherDenseModeAnchor (hn : 1 ≤ n) (i : HigherModes l)
    (T : InvertibleCut K (l + 1) n) : Matrix (Fin n) (Fin n) K :=
  denseAnchor (leftRegroup hn (0 : Fin (l + 1))) (rightRegroup i.2) (orientCut i.1 T)

def higherReciprocalBudget (hn : 1 ≤ n) (T : InvertibleCut K (l + 1) n) : ℕ :=
  ∑ i : HigherModes l, repeatedBudget (higherDenseModeAnchor hn i T).charpoly

def higherReciprocalAccepted (hn : 1 ≤ n) (T : Tensor K ((l + 1) + (l + 1)) n) : Prop :=
  ∃ h : IsUnit (flatten (l := l + 1) (r := l + 1) T),
    Fintype.card K ^ higherReciprocalBudget hn ⟨T, h⟩ ≤ n ^ ((l + 1) + (l + 1))

def higherReciprocalBad (hn : 1 ≤ n) (T : Tensor K ((l + 1) + (l + 1)) n) : Prop :=
  ∃ h : IsUnit (flatten (l := l + 1) (r := l + 1) T),
    n ^ ((l + 1) + (l + 1)) < Fintype.card K ^ higherReciprocalBudget hn ⟨T, h⟩

private theorem higher_mode_primary_mean (hl : 2 ≤ l) (hn : 200 ≤ n) (i : HigherModes l) :
    mean (fun T : InvertibleCut K (l + 1) n =>
      (repeatedBudget (higherDenseModeAnchor (by omega) i T).charpoly : ℝ)) ≤
      budgetConstant K + 9 := by
  let eL := leftRegroup (l := l) (n := n) (show 1 ≤ n by omega) 0
  let eR := rightRegroup (l := l) (n := n) i.2
  let o := orientCut (K := K) (s := l + 1) (n := n) i.1
  let B : ℝ := ↑(n^2)
  let δ : ℝ := 9 * anchorError K (Fin n)
  have hcap (A : Matrix (Fin n) (Fin n) K) : (repeatedBudget A.charpoly : ℝ) ≤ B :=
    primary_pointwise_cap A
  have hδ : B * δ ≤ 9 := by
    have h₁ : B * anchorError K (Fin n) ≤ 1 := by
      simpa only [B, anchorError, Fintype.card_fin] using
        (square_mul_field_decay (K := K) n (by omega : 2 ≤ n))
    calc
      B * δ = 9 * (B * anchorError K (Fin n)) := by dsimp [δ]; ring
      _ ≤ 9 := by linarith only [h₁]
  have h := higherOrder_reciprocal_coverage K l n hl hn 0 i.2 i.1
  by_cases h₂ : (2 : K) = 0
  · letI : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr (by simpa using h₂)
    have hL := h.1
    let f (y : AnchorTrace K (HigherRows l n) (Fin n)) : ℝ := repeatedBudget y.val.charpoly
    have hb := mean_comp_le_uniform_add_l1 (denseTraceAnchor eL eR ∘ o) f B δ
      (by dsimp [B]; positivity) (fun y => ⟨by dsimp [f]; positivity, hcap y.val⟩) hL
    have hm := mean_trace_budget_le (K := K) n (by omega) ((Fintype.card (HigherRows l n) : K)^2)
    exact hb.trans (add_le_add hm hδ)
  · let f (y : Matrix (Fin n) (Fin n) K) : ℝ := repeatedBudget y.charpoly
    have hb := mean_comp_le_uniform_add_l1 (denseAnchor eL eR ∘ o) f B δ
      (by dsimp [B]; positivity) (fun y => ⟨by dsimp [f]; positivity, hcap y⟩) (h.2 h₂)
    exact hb.trans (add_le_add (mean_matrix_budget_le (K := K) n) hδ)

/-- Combining all physical anchor budgets on the conditioned invertible
cut incurs a rejection bound independent of the number of modes. -/
theorem higherOrder_reciprocal_gate (hl : 2 ≤ l) (hn : 200 ≤ n) :
    event (fun T : InvertibleCut K (l + 1) n =>
      n ^ ((l + 1) + (l + 1)) < Fintype.card K ^ higherReciprocalBudget (by omega) T) ≤
      (budgetConstant K + 9) * Real.log (Fintype.card K) / Real.log n := by
  have hc : Fintype.card (HigherModes l) = (l + 1) + (l + 1) := by
    simp [HigherModes, two_mul]
  have h := event_pow_gate_le
    (fun (i : HigherModes l) (T : InvertibleCut K (l + 1) n) =>
      repeatedBudget (higherDenseModeAnchor (by omega) i T).charpoly)
    _ (higher_mode_primary_mean hl hn) (Fintype.card K) n Fintype.one_lt_card (by omega)
  simpa only [hc, higherReciprocalBudget] using h

private theorem higher_fraction_subtype_to_raw_le {A : Type*} [Finite A]
    (R : A → Prop) (P : {a : A // R a} → Prop) :
    uniformFraction A (fun a => ∃ h : R a, P ⟨a, h⟩) ≤ uniformFraction {a : A // R a} P := by
  let e : {a : A // ∃ h : R a, P ⟨a,h⟩} ≃ {x : {a : A // R a} // P x} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      exact ⟨⟨x.val, Classical.choose x.property⟩, Classical.choose_spec x.property⟩
    · intro x
      exact ⟨x.val.val, ⟨x.val.property, x.property⟩⟩
    · intro _
      exact Subtype.ext rfl
    · intro _
      exact Subtype.ext (Subtype.ext rfl)
  unfold uniformFraction
  rw [Nat.card_congr e]
  by_cases he : IsEmpty {a : A // R a}
  · letI : IsEmpty {x : {a : A // R a} // P x} := ⟨fun x => he.false x.val⟩
    simp only [Nat.card_of_isEmpty, Nat.cast_zero, zero_div, le_rfl]
  · letI : Nonempty {a : A // R a} := not_isEmpty_iff.mp he
    have h : Nat.card {a : A // R a} ≤ Nat.card A :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    apply div_le_div_of_nonneg_left (by positivity) _ (by exact_mod_cast h)
    exact_mod_cast Nat.card_pos (α := {a : A // R a})

private theorem higher_reciprocal_to_raw (hn : 1 ≤ n) :
    event (higherReciprocalBad (K := K) (l := l) hn) ≤
      event (fun T : InvertibleCut K (l + 1) n =>
        n ^ ((l + 1) + (l + 1)) < Fintype.card K ^ higherReciprocalBudget hn T) := by
  rw [event_as_fraction, event_as_fraction]
  exact higher_fraction_subtype_to_raw_le
    (fun T : Tensor K ((l + 1) + (l + 1)) n => IsUnit (flatten (l := l + 1) (r := l + 1) T))
    (fun T : InvertibleCut K (l + 1) n =>
      n ^ ((l + 1) + (l + 1)) < Fintype.card K ^ higherReciprocalBudget hn T)

/-- The unconditional raw-source probability that the cut is invertible
and the joint reciprocal primary gate fails. -/
theorem higherOrder_reciprocal_bad_le (hl : 2 ≤ l) (hn : 200 ≤ n) :
    event (higherReciprocalBad (K := K) (l := l) (show 1 ≤ n by omega)) ≤
      (budgetConstant K + 9) * Real.log (Fintype.card K) / Real.log n :=
  (higher_reciprocal_to_raw (K := K) (l := l) (by omega)).trans
    (higherOrder_reciprocal_gate (K := K) hl hn)

#print axioms higherOrder_reciprocal_gate
#print axioms higherOrder_reciprocal_bad_le

end
end Mathproof.EvenTI.Reciprocal.Coverage
