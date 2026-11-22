import Mathlib

namespace MarkedMultiplication

open scoped BigOperators

private theorem degree_sum {n : ℕ} (s : Finset (Fin n × Fin n))
    (f : Fin n × Fin n → Fin n) :
    (∑ j : Fin n, (s.filter fun e => f e = j).card) = s.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter s Finset.univ f

private theorem odd_positive_degrees_at_budget {n : ℕ} (degree : Fin n → ℕ)
    (budget : (∑ i, degree i) ≤ n) (parity : ∀ i, Odd (degree i)) :
    ∀ i, degree i = 1 := by
  have positive (i : Fin n) : 1 ≤ degree i :=
    Nat.succ_le_of_lt (parity i).pos
  intro i
  by_contra different
  have larger : 1 < degree i :=
    lt_of_le_of_ne (positive i) (fun h => different h.symm)
  have strict : (∑ _ : Fin n, (1 : ℕ)) < ∑ j, degree j :=
    Finset.sum_lt_sum (fun j _ => positive j) ⟨i, Finset.mem_univ i, larger⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id, mul_one] at strict
  exact (not_lt_of_ge budget) strict

/-- Odd parity in every bank and a budget of n edges characterize matchings. -/
theorem perfect_matching_iff_odd_with_budget {n : ℕ} (s : Finset (Fin n × Fin n)) :
    ((∀ i, (s.filter fun e => e.1 = i).card = 1) ∧
      (∀ j, (s.filter fun e => e.2 = j).card = 1)) ↔
    s.card ≤ n ∧ (∀ i, Odd (s.filter fun e => e.1 = i).card) ∧
      (∀ j, Odd (s.filter fun e => e.2 = j).card) := by
  constructor
  · rintro ⟨left, right⟩
    have total := degree_sum s Prod.fst
    have size : s.card = n := by
      simpa [left] using total.symm
    exact ⟨size.le, fun i => by rw [left]; decide, fun j => by rw [right]; decide⟩
  · rintro ⟨size, left, right⟩
    exact ⟨odd_positive_degrees_at_budget _ (by rwa [degree_sum s Prod.fst]) left,
      odd_positive_degrees_at_budget _ (by rwa [degree_sum s Prod.snd]) right⟩

end MarkedMultiplication
