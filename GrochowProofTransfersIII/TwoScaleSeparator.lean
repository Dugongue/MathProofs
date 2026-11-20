import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace TwoScaleSeparator

/-- The scalar interpolation selector underlying each coordinate filter. -/
noncomputable def selector {K : Type*} [Field K] [DecidableEq K]
    (grid : Finset K) (target x : K) : K :=
  ∏ a ∈ grid.erase target, (x - a) / (target - a)

theorem selector_at_target {K : Type*} [Field K] [DecidableEq K]
    (grid : Finset K) (t : K) : selector grid t t = 1 := by
  unfold selector
  apply Finset.prod_eq_one
  intro a ha
  exact div_self (sub_ne_zero.mpr (Finset.mem_erase.mp ha).1.symm)

theorem selector_at_other {K : Type*} [Field K] [DecidableEq K]
    (grid : Finset K) {t x : K} (hx : x ∈ grid) (hne : x ≠ t) :
    selector grid t x = 0 := by
  unfold selector
  exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hx⟩) (by simp)

theorem clean_numerator {R : Type*} [CommRing R] (e g s t u v : R) (d : ℕ)
    (hg : g = 1 + e * u) (hs : s = e ^ d * t + e ^ (d + 1) * v) :
    ∃ w : R, g ^ (d + 1) * s = e ^ d * t + e ^ (d + 1) * w := by
  have h : ∀ k : ℕ, ∃ a : R, g ^ k = 1 + e * a := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k hk =>
      obtain ⟨a, ha⟩ := hk
      refine ⟨a + u + e * a * u, ?_⟩
      rw [pow_succ, ha, hg]
      ring
  obtain ⟨a, ha⟩ := h (d + 1)
  refine ⟨a * t + v + e * a * v, ?_⟩
  rw [ha, hs]
  simp only [pow_succ]
  ring

theorem noisy_numerator {R : Type*} [CommRing R] (e g s u : R) (d : ℕ)
    (hg : g = e * u) :
    ∃ w : R, g ^ (d + 1) * s = e ^ (d + 1) * w := by
  exact ⟨u ^ (d + 1) * s, by rw [hg, mul_pow, mul_assoc]⟩

end TwoScaleSeparator
