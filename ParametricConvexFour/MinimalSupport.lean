import Mathlib.Data.Finset.Erase

namespace ParametricConvexFour

theorem minimal_of_failed_erasures {α : Type*} [DecidableEq α]
    {P : Finset α → Prop} (mono : Monotone P) (S : Finset α)
    (failed : ∀ a ∈ S, ¬ P (S.erase a)) :
    ∀ T ⊆ S, P T → T = S := by
  intro T hTS hT
  by_contra hne
  have hnst : ¬ S ⊆ T :=
    fun hST => hne (Finset.Subset.antisymm hTS hST)
  obtain ⟨a, haS, haT⟩ := Finset.not_subset.mp hnst
  exact failed a haS (mono (Finset.subset_erase.mpr ⟨hTS, haT⟩) hT)

end ParametricConvexFour
