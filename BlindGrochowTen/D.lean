import Mathlib

namespace BlindTen.PrimePower
open scoped BigOperators

/-- Profile entries count cycles of length p^i. -/
def mass (p : ℕ) (a : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), p ^ i * a i

def mark (p : ℕ) (a : ℕ → ℕ) (t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), p ^ i * a i

private theorem mark_succ (p : ℕ) (a : ℕ → ℕ) (t : ℕ) :
    mark p a (t + 1) = mark p a t + p ^ (t + 1) * a (t + 1) := by
  simp [mark, Finset.sum_range_succ]

private theorem mark_eq_all {p : ℕ} (hp : 1 < p) {a b : ℕ → ℕ} {k : ℕ}
    (h : ∀ t ≤ k, mark p a t = mark p b t) : ∀ i ≤ k, a i = b i := by
  intro i hi
  cases i with
  | zero => simpa [mark] using h 0 (Nat.zero_le k)
  | succ i =>
    have h0 := h i (by omega)
    have h1 := h (i + 1) hi
    rw [mark_succ, mark_succ, h0] at h1
    exact mul_left_cancel₀ (pow_ne_zero _ (by omega : p ≠ 0)) (Nat.add_left_cancel h1)

/-- With equal total dimension, observing marks up to j−1 suffices below p^(j+1).
At p^(j+1) there is a collision agreeing at every mark other than j. -/
theorem exact_punctured_mark_threshold {p j k : ℕ} (hp : 1 < p) (hjk : j < k) :
    (∀ a b : ℕ → ℕ, mass p a k = mass p b k → mass p a k < p ^ (j + 1) →
      (∀ t < j, mark p a t = mark p b t) → ∀ i ≤ k, a i = b i) ∧
    (∃ a b : ℕ → ℕ, mass p a k = p ^ (j + 1) ∧
      mass p b k = p ^ (j + 1) ∧ a j ≠ b j ∧
      ∀ t, t ≠ j → mark p a t = mark p b t) := by
  constructor
  · intro a b heq hsmall hprefix
    have ha (i : ℕ) (hli : j < i) (hik : i ≤ k) : a i = 0 := by
      by_contra hn
      have ht : p ^ i * a i ≤ mass p a k :=
        Finset.single_le_sum (f := fun u => p ^ u * a u)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hs : p ^ (j + 1) ≤ p ^ i * a i :=
        le_trans (Nat.pow_le_pow_right (by omega) (by omega))
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn))
      omega
    have hb (i : ℕ) (hli : j < i) (hik : i ≤ k) : b i = 0 := by
      by_contra hn
      have ht : p ^ i * b i ≤ mass p b k :=
        Finset.single_le_sum (f := fun u => p ^ u * b u)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
      have hs : p ^ (j + 1) ≤ p ^ i * b i :=
        le_trans (Nat.pow_le_pow_right (by omega) (by omega))
          (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hn))
      omega
    have collapse (c : ℕ → ℕ) (hc : ∀ i, j < i → i ≤ k → c i = 0)
        (t : ℕ) (hjt : j ≤ t) (htk : t ≤ k) : mark p c t = mark p c j := by
      induction t with
      | zero =>
        have hj : j = 0 := by omega
        simpa [hj]
      | succ t ih =>
        by_cases ht : t + 1 = j
        · rw [ht]
        · rw [mark_succ, hc _ (by omega) htk, mul_zero, add_zero]
          exact ih (by omega) (by omega)
    apply mark_eq_all hp
    intro t htk
    by_cases ht : t < j
    · exact hprefix t ht
    · rw [collapse a ha t (by omega) htk, collapse b hb t (by omega) htk]
      exact (collapse a ha k (by omega) le_rfl).symm.trans
        (heq.trans (collapse b hb k (by omega) le_rfl))
  · classical
    let a (i : ℕ) := if i = j then p else 0
    let b (i : ℕ) := if i = j + 1 then 1 else 0
    have aMark (t : ℕ) : mark p a t = if j ≤ t then p ^ (j + 1) else 0 := by
      simp [mark, a, mul_ite, Finset.sum_ite_eq', pow_succ]
    have bMark (t : ℕ) : mark p b t = if j + 1 ≤ t then p ^ (j + 1) else 0 := by
      simp [mark, b, mul_ite, Finset.sum_ite_eq']
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · simpa [mass, mark, Nat.le_of_lt hjk] using aMark k
    · simpa [mass, mark, hjk] using bMark k
    · simp [a, b, show p ≠ 0 by omega]
    · intro t ht
      rw [aMark, bMark]
      grind

/-- Nullity of P^(p^t)−I for p-primary permutation blocks, over any field. -/
def nullityProfile (p : ℕ) (a : ℕ → ℕ) (k t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), p ^ min i t * a i

private theorem nullity_step {p : ℕ} (hp : 1 < p) (a : ℕ → ℕ) (k t : ℕ) :
    nullityProfile p a k (t + 1) =
      nullityProfile p a k t +
        ((p - 1) * p ^ t) * ∑ i ∈ (Finset.range (k + 1)).filter (fun i => t < i), a i := by
  let weight := (p - 1) * p ^ t
  change _ = _ + weight * _
  rw [Finset.mul_sum, Finset.sum_filter]
  unfold nullityProfile
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : t < i
  · rw [if_pos h, Nat.min_eq_right (by omega), Nat.min_eq_right (by omega)]
    dsimp [weight]
    have he : p ^ (t + 1) = p ^ t + (p - 1) * p ^ t := by
      rw [pow_succ]
      have hd : p - 1 + 1 = p := by omega
      calc
        p ^ t * p = (p - 1 + 1) * p ^ t := by rw [hd, Nat.mul_comm]
        _ = p ^ t + (p - 1) * p ^ t := by ring
    rw [he, add_mul]
  · rw [if_neg h, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega), add_zero]

/-- The k+1 power nullities classify the entire p-primary cycle profile. -/
theorem cycle_profile_of_power_nullities {p : ℕ} (hp : 1 < p) {a b : ℕ → ℕ} {k : ℕ}
    (h : ∀ t ≤ k, nullityProfile p a k t = nullityProfile p b k t) :
    ∀ i ≤ k, a i = b i := by
  classical
  let tail (c : ℕ → ℕ) (i : ℕ) := ∑ u ∈ (Finset.range (k + 1)).filter (fun u => i ≤ u), c u
  have tails (i : ℕ) (hi : i ≤ k + 1) : tail a i = tail b i := by
    by_cases hi0 : i = 0
    · subst i
      simpa [nullityProfile, tail] using h 0 (Nat.zero_le k)
    by_cases helt : i ≤ k
    · obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
      have ht0 := h t (by omega)
      have ht1 := h (t + 1) helt
      rw [nullity_step hp, nullity_step hp, ht0] at ht1
      have hw : (p - 1) * p ^ t ≠ 0 := mul_ne_zero (by omega) (pow_ne_zero _ (by omega))
      simpa [tail, Nat.succ_le_iff] using mul_left_cancel₀ hw (Nat.add_left_cancel ht1)
    · have he : (Finset.range (k + 1)).filter (fun u => i ≤ u) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_range] at hu
        omega
      simp [tail, he]
  have tail_step (c : ℕ → ℕ) (i : ℕ) (hi : i ≤ k) : tail c i = c i + tail c (i + 1) := by
    have hset : (Finset.range (k + 1)).filter (fun u => i ≤ u) =
        insert i ((Finset.range (k + 1)).filter (fun u => i + 1 ≤ u)) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
      omega
    simp only [tail]
    rw [hset, Finset.sum_insert]
    simp
  intro i hi
  have he := tails i (by omega)
  rw [tail_step a i hi, tail_step b i hi, tails (i + 1) (by omega)] at he
  exact Nat.add_right_cancel he

end BlindTen.PrimePower
