import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace CevaWitnessCost

theorem two_coordinates_merge {A B : Type*} [AddMonoid A] [AddMonoid B]
    (a c : A) (b d : B) (ha : a ≠ 0) (hd : d ≠ 0) :
    (a ≠ 0 ∧ b ≠ 0) ∨ (c ≠ 0 ∧ d ≠ 0) ∨
      (a + c ≠ 0 ∧ b + d ≠ 0) := by
  classical
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · exact Or.inr (Or.inr (by simpa [hb, hc] using And.intro ha hd))
    · exact Or.inr (Or.inl ⟨hc, hd⟩)
  · exact Or.inl ⟨ha, hb⟩

theorem three_terminal_separation (a b c : ℤ)
    (h : (9 * a + 25 * b - 34 * c) % 30 = 1) :
    a ≠ b ∧ b ≠ c ∧ c ≠ a := by
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    omega
  · intro hbc
    omega
  · intro hca
    omega

theorem exact_three_terminal_character {X : Type*} (u v w : X) :
    (∃ f : X → ℤ, (9 * f u + 25 * f v - 34 * f w) % 30 = 1) ↔
      u ≠ v ∧ v ≠ w ∧ w ≠ u := by
  classical
  constructor
  · intro h
    obtain ⟨f, hf⟩ := h
    have hsep := three_terminal_separation (f u) (f v) (f w) hf
    exact ⟨fun h => hsep.1 (congrArg f h), fun h => hsep.2.1 (congrArg f h),
      fun h => hsep.2.2 (congrArg f h)⟩
  · intro h
    obtain ⟨huv, hvw, hwu⟩ := h
    let f : X → ℤ := fun x => if x = v then 1 else if x = w then 6 else 0
    refine ⟨f, ?_⟩
    norm_num [f, huv, hwu.symm, hvw.symm]

end CevaWitnessCost
