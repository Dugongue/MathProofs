import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace HozaGrochowIsolation

/-- If the cost of every path in a nonempty class grows by a common interval,
the minimum cost grows in the same interval, even if the minimizing path changes. -/
theorem min_increment {P : Type*} (old new : P → ℚ) (p₀ p₁ : P)
    (lower upper : ℚ) (min₀ : ∀ p, old p₀ ≤ old p) (min₁ : ∀ p, new p₁ ≤ new p)
    (growth : ∀ p, lower ≤ new p - old p ∧ new p - old p ≤ upper) :
    lower ≤ new p₁ - old p₀ ∧ new p₁ - old p₀ ≤ upper := by
  constructor
  · linarith [(min₀ p₁), (growth p₁).1]
  · linarith [(min₁ p₀), (growth p₀).2]

/-- The finite geometric tail used for the later seed digits. -/
theorem radix_tail_identity (n : ℕ) :
    (∑ i ∈ Finset.range n, (1 / 6 : ℚ) ^ (i + 1)) + (1 / 6 : ℚ) ^ n / 5 = 1 / 5 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have step : (1 / 6 : ℚ) ^ (n + 1) = (1 / 6 : ℚ) ^ n / 6 := by
        rw [pow_succ]
        ring
      rw [Finset.sum_range_succ, step]
      linarith

/-- The first differing seed digit with opposite code bits creates a gap
too large for the subsequent seed flips to erase. -/
theorem dominant_flip_separates
    (B firstSmall firstLarge finalSmall finalLarge : ℚ) (hB : 0 < B)
    (small : firstSmall ≤ B / 2) (large : B ≤ firstLarge)
    (tail : |(finalLarge - finalSmall) - (firstLarge - firstSmall)| ≤ 3 * B / 10) :
    finalSmall < finalLarge := by
  have ht := (abs_le.mp tail).1
  linarith

/-- The coefficient of the least weight in a path generating polynomial is
one in every coefficient semiring when precisely one index attains it. -/
theorem unique_minimum_count
    {P R : Type*} [Fintype P] [Semiring R] (cost : P → ℕ) (p : P)
    (strict : ∀ q : P, q ≠ p → cost p < cost q) :
    (∑ q : P, if cost q = cost p then (1 : R) else 0) = 1 := by
  classical
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hn
    simp [ne_of_gt (strict q hn)]
  · simp

/-- If every discarded coordinate has coefficient zero, the full row sum
equals the sum over the retained coordinates. -/
theorem forget_zero_coordinates
    {I R : Type*} [Fintype I] [Semiring R] (retained : Finset I)
    (coefficient input : I → R) (h : ∀ i, i ∉ retained → coefficient i = 0) :
    ∑ i ∈ retained, coefficient i * input i = ∑ i, coefficient i * input i := by
  classical
  apply Finset.sum_subset (Finset.subset_univ retained)
  intro i _ hi
  simp [h i hi]

/-- A common selector avoids every nonzero coefficient vector exactly when
the ground-field dimension is at least the number of selector coordinates. -/
theorem shared_selector_dimension
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [Module.Finite K E] (k : ℕ) :
    (∃ v : Fin k → E, ∀ c : Fin k → K,
      (∃ i, c i ≠ 0) → (∑ i, c i • v i) ≠ 0) ↔ k ≤ Module.finrank K E := by
  constructor
  · rintro ⟨v, hv⟩
    have independent : LinearIndependent K v := Fintype.linearIndependent_iff.mpr <| by
      intro c hc i
      by_contra h
      exact hv c ⟨i, h⟩ hc
    simpa using independent.fintype_card_le_finrank
  · intro hk
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := K) (M := E) hk
    refine ⟨v, fun c ⟨i, hi⟩ hz => hi ?_⟩
    exact Fintype.linearIndependent_iff.mp hv c hz i

end HozaGrochowIsolation
