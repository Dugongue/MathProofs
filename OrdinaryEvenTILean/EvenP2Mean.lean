import EvenPrimaryMarginal
import EvenLiveSingularBlock

namespace Mathproof.EvenTI.Singular.Coverage

open scoped BigOperators Classical
open EvenTI.Primary Mathproof.EvenOrdinaryTISingular

noncomputable section

theorem event_as_fraction {A : Type*} [Fintype A] (P : A → Prop) :
    event P = uniformFraction A P := event_eq_card P

theorem mean_cost_le_of_events {A B Y : Type*}
    [Fintype A] [Fintype B] [Fintype Y] (f : A → Y) (g : B → Y)
    (cost : Y → ℝ) (M δ : ℝ) (hM : 0 ≤ M)
    (hc : ∀ y, 0 ≤ cost y ∧ cost y ≤ M)
    (h : ∀ P : Y → Prop, uniformFraction A (fun a => P (f a)) ≤
      uniformFraction B (fun b => P (g b)) + δ) :
    mean (cost ∘ f) ≤ mean (cost ∘ g) + M * δ := by
  let P (y : Y) : Prop := weight g y ≤ weight f y
  let z (y : Y) := weight f y - weight g y
  have he (u : A → Y) :
      event (fun a => P (u a)) = ∑ y, (if P y then 1 else 0) * weight u y :=
    mean_comp_eq_weight u (fun y => if P y then 1 else 0)
  have he' (u : B → Y) :
      event (fun b => P (u b)) = ∑ y, (if P y then 1 else 0) * weight u y :=
    mean_comp_eq_weight u (fun y => if P y then 1 else 0)
  have hp := h P
  rw [← event_as_fraction, ← event_as_fraction, he, he'] at hp
  have hsum : (∑ y, (if P y then 1 else 0) * z y) ≤ δ := by
    simp only [z, mul_sub, Finset.sum_sub_distrib]
    linarith
  have ht (y : Y) : cost y * z y ≤ M * ((if P y then 1 else 0) * z y) := by
    by_cases hy : P y
    · have hz : 0 ≤ z y := sub_nonneg.mpr hy
      simpa only [if_pos hy, one_mul] using mul_le_mul_of_nonneg_right (hc y).2 hz
    · have hz : z y ≤ 0 := sub_nonpos.mpr (le_of_lt (lt_of_not_ge hy))
      simpa only [if_neg hy, zero_mul, mul_zero] using mul_nonpos_of_nonneg_of_nonpos (hc y).1 hz
  have hsum' := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => ht y)
  rw [← Finset.mul_sum] at hsum'
  have hh := hsum'.trans (mul_le_mul_of_nonneg_left hsum hM)
  simp only [z, mul_sub, Finset.sum_sub_distrib, ← mean_comp_eq_weight] at hh
  linarith

#print axioms mean_cost_le_of_events

end
end Mathproof.EvenTI.Singular.Coverage
