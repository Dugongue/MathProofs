import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic

open scoped BigOperators

namespace BalancedTensorRankBands

/-- The identity rank for a zero-based marker index. -/
def weight (D k i : ℕ) : ℕ :=
  (k + i + 2) * (D + 1)

/-- The contraction rank is this tag contribution plus the rank off the tags. -/
def rankScore {k : ℕ} (D : ℕ) (support : Finset (Fin k)) (residual : ℕ) : ℕ :=
  (∑ i ∈ support, weight D k i.val) + residual

private theorem min_weight_le (D k i : ℕ) : weight D k 0 ≤ weight D k i :=
  Nat.mul_le_mul_right (D + 1) (by omega)

private theorem residual_lt_min_weight (D k : ℕ) : D < weight D k 0 := by
  have h := Nat.mul_le_mul_right (D + 1) (show 1 ≤ k + 0 + 2 by omega)
  simp only [Nat.one_mul] at h
  exact lt_of_lt_of_le (Nat.lt_succ_self D) h

private theorem single_weight_gap (D k : ℕ) {i j : ℕ} (hij : i < j) :
    weight D k i + D < weight D k j := by
  have h := Nat.mul_le_mul_right (D + 1) (show k + i + 2 + 1 ≤ k + j + 2 by omega)
  rw [Nat.add_mul, Nat.one_mul] at h
  change weight D k i + (D + 1) ≤ weight D k j at h
  omega

private theorem single_weight_bound (D k : ℕ) (i : Fin k) :
    weight D k i.val + D < weight D k 0 + weight D k 0 := by
  have hi := i.isLt
  have h := Nat.mul_le_mul_right (D + 1)
    (show k + i.val + 2 + 1 ≤ (k + 0 + 2) + (k + 0 + 2) by omega)
  rw [Nat.add_mul, Nat.one_mul, Nat.add_mul (k + 0 + 2) (k + 0 + 2)] at h
  change weight D k i.val + (D + 1) ≤ weight D k 0 + weight D k 0 at h
  omega

/-- The low-rank threshold detects exactly the absence of all markers. -/
theorem core_iff_empty (D k : ℕ) (support : Finset (Fin k)) (residual : ℕ)
    (hr : residual ≤ D) : rankScore D support residual ≤ D ↔ support = ∅ := by
  constructor
  · intro h
    by_contra hne
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hsum : weight D k i.val ≤ ∑ j ∈ support, weight D k j.val :=
      Finset.single_le_sum_of_canonicallyOrdered (f := fun j => weight D k j.val) hi
    have hmin := min_weight_le D k i.val
    have hres := residual_lt_min_weight D k
    unfold rankScore at h
    omega
  · rintro rfl
    simpa [rankScore] using hr

/-- The band assigned to one marker detects exactly that singleton support. -/
theorem band_iff_singleton (D k : ℕ) (support : Finset (Fin k)) (residual : ℕ)
    (hr : residual ≤ D) (i : Fin k) :
    (weight D k i.val ≤ rankScore D support residual ∧
      rankScore D support residual ≤ weight D k i.val + D) ↔ support = {i} := by
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : support ≠ ∅ := by
      intro he
      simp [rankScore, he] at hlo
      have hmin := min_weight_le D k i.val
      have hres := residual_lt_min_weight D k
      omega
    have hc : support.card ≤ 1 := by
      by_contra! h
      obtain ⟨j, hj, l, hl, hjl⟩ := Finset.one_lt_card.mp h
      have hsub : ({j, l} : Finset (Fin k)) ⊆ support := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hj
        · exact hl
      have hsum : (∑ u ∈ ({j, l} : Finset (Fin k)), weight D k u.val) ≤
          ∑ u ∈ support, weight D k u.val :=
        Finset.sum_le_sum_of_subset hsub
      have hjl' : j ∉ ({l} : Finset (Fin k)) := by simpa using hjl
      simp only [Finset.sum_insert hjl', Finset.sum_singleton] at hsum
      have hjMin := min_weight_le D k j.val
      have hlMin := min_weight_le D k l.val
      have hiMax := single_weight_bound D k i
      unfold rankScore at hhi
      omega
    have hp : 0 < support.card :=
      Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn)
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp (show support.card = 1 by omega)
    simp only [rankScore, Finset.sum_singleton] at hlo hhi
    have hval : j.val = i.val := by
      rcases lt_trichotomy j.val i.val with h | h | h
      · have hgap := single_weight_gap D k h
        omega
      · exact h
      · have hgap := single_weight_gap D k h
        omega
    rw [Fin.ext hval]
  · rintro rfl
    simp only [rankScore, Finset.sum_singleton]
    omega

end BalancedTensorRankBands
