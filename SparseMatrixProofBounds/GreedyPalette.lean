import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace GramInputs

/-- A finite ordered palette construction. Earlier choices may forbid different
colors for each later choice. A bound on their total counts suffices. -/
theorem ordered_palette (n : ℕ) (palette : Finset ℕ)
    (ban : ℕ → ℕ → ℕ → Finset ℕ)
    (budget : ∀ i < n, ∀ c : ℕ → ℕ,
      (∑ j ∈ Finset.range i, (ban i j (c j)).card) < palette.card) :
    ∃ c : ℕ → ℕ, ∀ i < n, c i ∈ palette ∧ ∀ j < i, c i ∉ ban i j (c j) := by
  induction n with
  | zero => exact ⟨fun _ => 0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (fun i hi => budget i (Nat.lt_succ_of_lt hi))
    let forbidden := (Finset.range n).biUnion (fun j => ban n j (c j))
    have hcard : forbidden.card < palette.card :=
      lt_of_le_of_lt Finset.card_biUnion_le (budget n (Nat.lt_succ_self n) c)
    obtain ⟨x, hx, hxFree⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    refine ⟨fun i => if i = n then x else c i, ?_⟩
    intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · obtain ⟨hold, hban⟩ := hc i hlt
      refine ⟨by simpa [Nat.ne_of_lt hlt] using hold, ?_⟩
      intro j hj
      simpa [Nat.ne_of_lt hlt, Nat.ne_of_lt (hj.trans hlt)] using hban j hj
    · refine ⟨by simpa using hx, ?_⟩
      intro j hj
      simp only [if_pos rfl, if_neg (Nat.ne_of_lt hj)]
      exact fun he => hxFree (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, he⟩)

end GramInputs
