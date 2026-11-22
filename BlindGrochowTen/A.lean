import Mathlib

namespace BlindGrochowTen
namespace MarkRecovery

def readout (s : Finset ℕ) (accepts : ℕ → Prop) [DecidablePred accepts]
    (a : ℕ → ℕ) : ℕ :=
  ∑ d ∈ s, if accepts d then d * a d else 0

private theorem equal_readout_off {s : Finset ℕ} {d : ℕ}
    {accepts : ℕ → Prop} [DecidablePred accepts] {a b : ℕ → ℕ}
    (h : ∀ e ∈ s, e ≠ d → accepts e → a e = b e) :
    readout (s.erase d) accepts a = readout (s.erase d) accepts b := by
  unfold readout
  apply Finset.sum_congr rfl
  intro e he
  obtain ⟨hne, hes⟩ := Finset.mem_erase.mp he
  by_cases hp : accepts e
  · simp [hp, h e hes hne hp]
  · simp [hp]

private theorem readout_split {s : Finset ℕ} {d : ℕ}
    {accepts : ℕ → Prop} [DecidablePred accepts] (a : ℕ → ℕ)
    (hd : d ∈ s) (h : accepts d) :
    readout s accepts a = readout (s.erase d) accepts a + d * a d := by
  unfold readout
  convert (Finset.sum_erase_add s (fun e => if accepts e then e * a e else 0) hd).symm using 1
  simp [h]

private theorem recover_single_entry {s : Finset ℕ} {d : ℕ}
    {accepts : ℕ → Prop} [DecidablePred accepts] {a b : ℕ → ℕ}
    (hd : d ∈ s) (hself : accepts d)
    (hoff : ∀ e ∈ s, e ≠ d → accepts e → a e = b e)
    (hab : readout s accepts a < readout s accepts b + d)
    (hba : readout s accepts b < readout s accepts a + d) :
    a d = b d := by
  rw [readout_split a hd hself, readout_split b hd hself, equal_readout_off hoff] at hab hba
  rcases lt_trichotomy (a d) (b d) with h | h | h
  · have hm : d * (a d + 1) ≤ d * b d :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  · exact h
  · have hm : d * (b d + 1) ≤ d * a d :=
      Nat.mul_le_mul_left _ (Nat.succ_le_of_lt h)
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

def mark (s : Finset ℕ) (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  readout s (· ∣ n) a

/-- Different supported profiles have a mark discrepancy of at least the
smallest differing length, even using a different exponent to sample each row. -/
theorem robust_divisor_recovery {s : Finset ℕ} {a b : ℕ → ℕ} (sample : ℕ → ℕ)
    (hpos : ∀ d ∈ s, 0 < d)
    (hrow : ∀ d ∈ s, ∀ e ∈ s, (e ∣ sample d) ↔ (e ∣ d))
    (hab : ∀ d ∈ s, mark s a (sample d) < mark s b (sample d) + d)
    (hba : ∀ d ∈ s, mark s b (sample d) < mark s a (sample d) + d) :
    ∀ d ∈ s, a d = b d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    apply recover_single_entry (accepts := fun e => e ∣ sample d) hd
      ((hrow d hd d hd).mpr (dvd_refl d))
    · intro e he hne hes
      have hle := Nat.le_of_dvd (hpos d hd) ((hrow d hd e he).mp hes)
      exact ih e (Nat.lt_of_le_of_ne hle hne) he
    · exact hab d hd
    · exact hba d hd

/-- A vector of mark observations stored as digits in one natural number. -/
def pack (base : ℕ) (observations : ℕ → ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: rest => observations d + base * pack base observations rest

private theorem pack_digits {base : ℕ} (hbase : 0 < base)
    {x y : ℕ → ℕ} {cells : List ℕ}
    (hx : ∀ d ∈ cells, x d < base) (hy : ∀ d ∈ cells, y d < base)
    (h : pack base x cells = pack base y cells) :
    ∀ d ∈ cells, x d = y d := by
  induction cells with
  | nil => simp
  | cons d rest ih =>
    simp only [pack] at h
    have first : x d = y d := by
      have hm := congrArg (· % base) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hx d (by simp)),
        Nat.mod_eq_of_lt (hy d (by simp))] using hm
    rw [first] at h
    have ht : pack base x rest = pack base y rest :=
      Nat.eq_of_mul_eq_mul_left hbase (Nat.add_left_cancel h)
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact first
    · exact ih (fun i hi => hx i (List.mem_cons_of_mem d hi))
        (fun i hi => hy i (List.mem_cons_of_mem d hi)) ht v hv

/-- Within a known size bound, the base-encoding of tailored mark rows
determines the whole positive-length profile. -/
theorem packed_marks_recovery {s : Finset ℕ} {a b : ℕ → ℕ} {bound : ℕ}
    (cells : List ℕ) (sample : ℕ → ℕ)
    (hcover : ∀ d ∈ s, d ∈ cells)
    (hpos : ∀ d ∈ s, 0 < d)
    (hrow : ∀ d ∈ s, ∀ e ∈ s, (e ∣ sample d) ↔ (e ∣ d))
    (ha : ∑ d ∈ s, d * a d ≤ bound)
    (hb : ∑ d ∈ s, d * b d ≤ bound)
    (h : pack (bound + 1) (fun d => mark s a (sample d)) cells =
      pack (bound + 1) (fun d => mark s b (sample d)) cells) :
    ∀ d ∈ s, a d = b d := by
  have hbnd (z : ℕ → ℕ) (hz : ∑ d ∈ s, d * z d ≤ bound) (n : ℕ) :
      mark s z n < bound + 1 := by
    unfold mark readout
    apply Nat.lt_succ_of_le
    apply le_trans _ hz
    apply Finset.sum_le_sum
    intro e he
    split
    · exact le_rfl
    · exact Nat.zero_le _
  have eq := pack_digits (Nat.succ_pos bound) (fun d _ => hbnd a ha (sample d))
    (fun d _ => hbnd b hb (sample d)) h
  refine robust_divisor_recovery sample hpos hrow ?_ ?_
  · intro d hd
    rw [eq d (hcover d hd)]
    exact Nat.lt_add_of_pos_right (hpos d hd)
  · intro d hd
    rw [eq d (hcover d hd)]
    exact Nat.lt_add_of_pos_right (hpos d hd)

def polynomialMark (terms : Finset ℕ) (coefficient : ℕ → ℕ) (value : ℕ) : ℕ :=
  ∑ j ∈ terms, coefficient j * value ^ j

private theorem polynomial_gap {terms : Finset ℕ} {coefficient : ℕ → ℕ} {j a b gap : ℕ}
    (hj : j ∈ terms) (hjpos : 0 < j) (h : a + gap ≤ b) :
    polynomialMark terms coefficient a + coefficient j * gap ^ j ≤
      polynomialMark terms coefficient b := by
  have hpow := le_trans
    (pow_add_pow_le (Nat.zero_le a) (Nat.zero_le gap) (Nat.ne_of_gt hjpos))
    (Nat.pow_le_pow_left h j)
  have hone := Nat.mul_le_mul_left (coefficient j) hpow
  rw [Nat.mul_add] at hone
  have hrest : (∑ i ∈ terms.erase j, coefficient i * a ^ i) ≤
      ∑ i ∈ terms.erase j, coefficient i * b ^ i := by
    apply Finset.sum_le_sum
    intro i hi
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) i)
  unfold polynomialMark
  rw [← Finset.sum_erase_add terms (fun i => coefficient i * a ^ i) hj,
    ← Finset.sum_erase_add terms (fun i => coefficient i * b ^ i) hj]
  omega

/-- Tests by polynomial operations on the Cartesian powers of a profile may
amplify the minimum first-error gap from d to coefficient(d,j) * d^j. -/
theorem robust_polynomial_marks_recovery {s : Finset ℕ} {a b : ℕ → ℕ}
    (sample selected : ℕ → ℕ) (terms : ℕ → Finset ℕ) (coefficient : ℕ → ℕ → ℕ)
    (hpos : ∀ d ∈ s, 0 < d)
    (hrow : ∀ d ∈ s, ∀ e ∈ s, (e ∣ sample d) ↔ (e ∣ d))
    (hselected : ∀ d ∈ s, selected d ∈ terms d ∧ 0 < selected d)
    (hab : ∀ d ∈ s, polynomialMark (terms d) (coefficient d) (mark s a (sample d)) <
      polynomialMark (terms d) (coefficient d) (mark s b (sample d)) +
        coefficient d (selected d) * d ^ selected d)
    (hba : ∀ d ∈ s, polynomialMark (terms d) (coefficient d) (mark s b (sample d)) <
      polynomialMark (terms d) (coefficient d) (mark s a (sample d)) +
        coefficient d (selected d) * d ^ selected d) :
    ∀ d ∈ s, a d = b d := by
  refine robust_divisor_recovery sample hpos hrow ?_ ?_
  · intro d hd
    by_contra! h
    exact (not_lt_of_ge (polynomial_gap (hselected d hd).1 (hselected d hd).2 h)) (hab d hd)
  · intro d hd
    by_contra! h
    exact (not_lt_of_ge (polynomial_gap (hselected d hd).1 (hselected d hd).2 h)) (hba d hd)

private theorem recover_leaf_fibre {W : Type*} [DecidableEq W] {s : Finset ℕ} {a b : ℕ → ℕ}
    (f : ℕ → W) {d : ℕ} (hd : d ∈ s) (hpos : 0 < d)
    (hs : ∀ e ∈ s, a e ≠ b e → f e = f d → e = d)
    (hobs : readout s (fun j => f j = f d) a = readout s (fun j => f j = f d) b) :
    a d = b d := by
  apply recover_single_entry (accepts := fun j => f j = f d) hd rfl
  · intro e he hed hfibre
    by_contra hn
    exact hed (hs e he hn hfibre)
  · rw [hobs]
    exact Nat.lt_add_of_pos_right hpos
  · rw [hobs]
    exact Nat.lt_add_of_pos_right hpos

section TwoDecks
variable {U V : Type*} [DecidableEq U] [DecidableEq V]

/-- Two extension decks determine a profile on a prescribed support when every
nonempty sub-support has an edge alone in a fibre on at least one side. -/
theorem two_decks_forest_recovery {s : Finset ℕ} {a b : ℕ → ℕ}
    (left : ℕ → U) (right : ℕ → V)
    (hpos : ∀ d ∈ s, 0 < d)
    (hforest : ∀ t ⊆ s, t.Nonempty → ∃ d ∈ t,
      (∀ e ∈ t, left e = left d → e = d) ∨
      (∀ e ∈ t, right e = right d → e = d))
    (hleft : ∀ u, readout s (fun d => left d = u) a =
      readout s (fun d => left d = u) b)
    (hright : ∀ v, readout s (fun d => right d = v) a =
      readout s (fun d => right d = v) b) :
    ∀ d ∈ s, a d = b d := by
  classical
  by_contra! hn
  let t := s.filter (fun d => a d ≠ b d)
  have ht : t.Nonempty := by
    obtain ⟨d, hd, hne⟩ := hn
    exact ⟨d, Finset.mem_filter.mpr ⟨hd, hne⟩⟩
  obtain ⟨d, hdt, hf⟩ := hforest t (Finset.filter_subset _ _) ht
  obtain ⟨hd, hne⟩ := Finset.mem_filter.mp hdt
  rcases hf with hl | hr
  · exact hne (recover_leaf_fibre left hd (hpos d hd)
      (fun e he hne' => hl e (Finset.mem_filter.mpr ⟨he, hne'⟩)) (hleft (left d)))
  · exact hne (recover_leaf_fibre right hd (hpos d hd)
      (fun e he hne' => hr e (Finset.mem_filter.mpr ⟨he, hne'⟩)) (hright (right d)))

end TwoDecks
end MarkRecovery
end BlindGrochowTen
