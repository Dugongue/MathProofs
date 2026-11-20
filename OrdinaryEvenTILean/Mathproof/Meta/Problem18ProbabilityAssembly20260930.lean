import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Abel

/-!
# Finite probability assembly for Problem 1.8

These lemmas isolate two assembly steps used by the written proof:
second-moment transfer from a uniform reference law, and cancellation between
the number of spectral subspaces and each conditioned block probability.
-/

namespace Mathproof.Problem18ProbabilityAssembly20260930

open scoped BigOperators

theorem sqrt_transfer_core
    (N C e s : ℝ) (hN : 0 < N) (hC : 0 ≤ C) (he : 0 ≤ e)
    (hs : 0 ≤ s) (h2 : s ^ 2 ≤ C * e * N) :
    s / N ≤ Real.sqrt (C * (e / N)) := by
  have hCN : 0 ≤ C * (e / N) := by positivity
  apply (Real.le_sqrt (by positivity) hCN).2
  calc
    (s / N) ^ 2 = s ^ 2 / (N ^ 2) := by ring
    _ ≤ (C * e * N) / (N ^ 2) := by
      exact div_le_div_of_nonneg_right h2 (sq_nonneg N)
    _ = C * (e / N) := by field_simp

/-- A density with bounded uniform second moment transfers a uniform event
bound with the square-root loss used in Section 8.5. -/
theorem weighted_event_probability_le_sqrt
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (ρ : Ω → ℝ) (E : Finset Ω) (C : ℝ)
    (hρ : ∀ x, 0 ≤ ρ x) (hC : 0 ≤ C)
    (hsecond : ∑ x, (ρ x) ^ 2 ≤ C * Fintype.card Ω) :
    (∑ x ∈ E, ρ x) / Fintype.card Ω ≤
      Real.sqrt (C * ((E.card : ℝ) / Fintype.card Ω)) := by
  have hsub :
      ∑ x ∈ E, (ρ x) ^ 2 ≤ ∑ x, (ρ x) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
    intro x hx hnx
    positivity
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq E (fun _ => (1 : ℝ)) ρ
  have hsq :
      (∑ x ∈ E, ρ x) ^ 2 ≤
        C * (E.card : ℝ) * Fintype.card Ω := by
    calc
      (∑ x ∈ E, ρ x) ^ 2 ≤
          (E.card : ℝ) * ∑ x ∈ E, (ρ x) ^ 2 := by
        simpa using hcs
      _ ≤ (E.card : ℝ) * (C * Fintype.card Ω) := by
        exact mul_le_mul_of_nonneg_left (hsub.trans hsecond) (by positivity)
      _ = C * (E.card : ℝ) * Fintype.card Ω := by ring
  apply sqrt_transfer_core (Fintype.card Ω) C E.card
    (∑ x ∈ E, ρ x)
  · positivity
  · exact hC
  · positivity
  · exact Finset.sum_nonneg fun x hx => hρ x
  · exact hsq

/-- The probability of a finite union is at most the sum of its component
probabilities, stated directly for uniform finite sample spaces. -/
theorem family_union_probability_le
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    [DecidableEq Ω] [DecidableEq I]
    (E : I → Finset Ω) :
    (((Finset.univ : Finset I).biUnion E).card : ℝ) /
        Fintype.card Ω ≤
      ∑ i : I, ((E i).card : ℝ) / Fintype.card Ω := by
  have hcard :
      ((((Finset.univ : Finset I).biUnion E).card : ℕ) : ℝ) ≤
        ((∑ i : I, (E i).card : ℕ) : ℝ) := by
    exact_mod_cast (Finset.card_biUnion_le :
      ((Finset.univ : Finset I).biUnion E).card ≤
        ∑ i ∈ (Finset.univ : Finset I), (E i).card)
  calc
    _ ≤ ((∑ i : I, (E i).card : ℕ) : ℝ) / Fintype.card Ω :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = ∑ i : I, ((E i).card : ℝ) / Fintype.card Ω := by
      rw [Nat.cast_sum, Finset.sum_div]

/-- If there are at most c*q candidate blocks and every conditioned bad
block has probability at most q⁻¹*eps, their union has probability at most
c*eps. This is the exact cancellation used in Section 9. -/
theorem family_union_probability_cancellation
    {Ω I : Type*} [Fintype Ω] [Nonempty Ω] [Fintype I]
    [DecidableEq Ω] [DecidableEq I]
    (E : I → Finset Ω) (q c eps : ℝ)
    (hq : 0 < q) (hc : 0 ≤ c) (heps : 0 ≤ eps)
    (hI : (Fintype.card I : ℝ) ≤ c * q)
    (hE : ∀ i : I,
      ((E i).card : ℝ) / Fintype.card Ω ≤ q⁻¹ * eps) :
    (((Finset.univ : Finset I).biUnion E).card : ℝ) /
        Fintype.card Ω ≤ c * eps := by
  calc
    _ ≤ ∑ i : I, ((E i).card : ℝ) / Fintype.card Ω :=
      family_union_probability_le E
    _ ≤ ∑ _i : I, q⁻¹ * eps := by
      exact Finset.sum_le_sum fun i hi => hE i
    _ = (Fintype.card I : ℝ) * (q⁻¹ * eps) := by simp
    _ ≤ (c * q) * (q⁻¹ * eps) := by
      exact mul_le_mul_of_nonneg_right hI (mul_nonneg (inv_nonneg.mpr hq.le) heps)
    _ = c * eps := by field_simp

/-- Two source-side good conditions may be assembled without any independence
assumption: failure of their conjunction is contained in the union of the two
failure events. -/
theorem conjunction_failure_probability_le
    {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    (E F : Finset Ω) (a b : ℝ)
    (hE : (E.card : ℝ) / Fintype.card Ω ≤ a)
    (hF : (F.card : ℝ) / Fintype.card Ω ≤ b) :
    ((E ∪ F).card : ℝ) / Fintype.card Ω ≤ a + b := by
  have hcard : (((E ∪ F).card : ℕ) : ℝ) ≤ E.card + F.card := by
    exact_mod_cast Finset.card_union_le E F
  calc
    ((E ∪ F).card : ℝ) / Fintype.card Ω ≤
        ((E.card : ℝ) + F.card) / Fintype.card Ω :=
      div_le_div_of_nonneg_right hcard (by positivity)
    _ = (E.card : ℝ) / Fintype.card Ω +
        (F.card : ℝ) / Fintype.card Ω := by ring
    _ ≤ a + b := add_le_add hE hF
end Mathproof.Problem18ProbabilityAssembly20260930


