import Mathlib.Data.Nat.Choose.Sum

open scoped BigOperators

namespace IsotropicDetection

/-- On equal-cardinality subsets the indicated integral combination of containment
tests extracts a single coefficient. This is the combinatorial step for isotropic minors. -/
theorem isolate {α : Type*} [DecidableEq α] (u i j : Finset α)
    (hj : j ⊆ u) (hc : i.card = j.card) :
    (∑ t ∈ (u \ i).powerset, if t ⊆ j then (-1 : ℤ) ^ t.card else 0) =
      if i = j then 1 else 0 := by
  rw [← Finset.sum_filter]
  have hsets : ((u \ i).powerset.filter (fun t => t ⊆ j)) = (j \ i).powerset := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hu, hsub⟩ x hx
      exact Finset.mem_sdiff.mpr ⟨hsub hx, (Finset.mem_sdiff.mp (hu hx)).2⟩
    · intro h
      exact ⟨fun x hx => Finset.mem_sdiff.mpr
        ⟨hj (Finset.mem_sdiff.mp (h hx)).1, (Finset.mem_sdiff.mp (h hx)).2⟩,
        fun x hx => (Finset.mem_sdiff.mp (h hx)).1⟩
  rw [hsets, Finset.sum_powerset_neg_one_pow_card]
  have hiff : j \ i = ∅ ↔ i = j := by
    rw [Finset.sdiff_eq_empty_iff_subset]
    exact ⟨fun h => (Finset.eq_of_subset_of_card_le h hc.le).symm,
      fun h => h ▸ Finset.Subset.rfl⟩
  simp only [hiff]

end IsotropicDetection
