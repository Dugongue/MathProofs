import Mathproof.MinimumGenerationGreedyOrdinal

namespace Mathproof.MinimumGeneration.PhysicalGreedyReplay

variable {n : Nat}

/-- Search for one accepted ordinal, restarting strictly after each returned label. -/
def byNext (query : (Fin n → Bool) → Fin n → Bool) (eligible : Fin n → Bool)
    (start : Nat) : Nat → Option (Fin n)
  | 0 => GreedyGenerator.next query eligible start
  | i + 1 =>
    match GreedyGenerator.next query eligible start with
    | none => none
    | some x => byNext query eligible (x.val+1) i

private theorem next_step (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Fin n → Bool) {k : Nat} (hk : k < n) :
    GreedyGenerator.next query eligible k =
      if GreedyGenerator.accept query eligible ⟨k, hk⟩ then some ⟨k, hk⟩
      else GreedyGenerator.next query eligible (k+1) := by
  unfold GreedyGenerator.next
  conv_lhs => rw [show n - k = (n - (k+1)) + 1 by omega]
  simp only [ChiefExecution.firstHitFrom, dif_pos hk]

theorem byNext_eq_ordinal (query : (Fin n → Bool) → Fin n → Bool)
    (eligible : Fin n → Bool) (start i : Nat) :
    byNext query eligible start i =
      GreedyOrdinal.ordinal (GreedyGenerator.accept query eligible) start (n-start) i := by
  by_cases hl : start < n
  · rw [show n - start = n - (start+1)+1 by omega]
    by_cases ha : GreedyGenerator.accept query eligible ⟨start, hl⟩ = true
    · cases i with
      | zero => simp [byNext, next_step query eligible hl, GreedyOrdinal.ordinal, hl, ha]
      | succ i =>
        simp only [byNext, next_step query eligible hl, ha, if_true, GreedyOrdinal.ordinal, dif_pos hl]
        exact byNext_eq_ordinal query eligible (start+1) i
    · have shift : byNext query eligible start i = byNext query eligible (start+1) i := by
        cases i <;> simp [byNext, next_step query eligible hl, ha]
      rw [shift, byNext_eq_ordinal query eligible (start+1) i]
      simp [GreedyOrdinal.ordinal, hl, ha]
  · have hzero : n - start = 0 := by omega
    cases i <;> simp [byNext, GreedyGenerator.next, hzero, ChiefExecution.firstHitFrom, GreedyOrdinal.ordinal]
termination_by n - start
decreasing_by all_goals omega

end Mathproof.MinimumGeneration.PhysicalGreedyReplay
