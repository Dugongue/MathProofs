import Mathlib

namespace PrincipalUnitFour.Precision

/-- The labels over a quotient label with the specified payload class. -/
def colorFibre {G H C : Type*} [Monoid G] [Monoid H]
    [Fintype G] [DecidableEq H] [DecidableEq C]
    (π : G →* H) (color : G → C) (b : H) (c : C) : Finset G :=
  Finset.univ.filter fun a => π a = b ∧ color a = c

/-- If colors encode the inverse images of subgroup cosets, their collapsed
multiplicities have exactly that subgroup as translation stabilizer. -/
theorem coset_colors_exact_translation_stabilizer
    {G H C : Type*} [Group G] [Group H] [Fintype G] [DecidableEq H] [DecidableEq C]
    (π : G →* H) (hπ : Function.Surjective π) (color : G → C)
    (K : Subgroup H)
    (hcolor : ∀ a b, color a = color b ↔ π a / π b ∈ K)
    (h : H) :
    (∀ b c, (colorFibre π color (h * b) c).card = (colorFibre π color b c).card) ↔
      h ∈ K := by
  constructor
  · intro htrans
    have hbase : 0 < (colorFibre π color 1 (color 1)).card := by
      apply Finset.card_pos.mpr
      exact ⟨1, by simp [colorFibre]⟩
    have ht := htrans 1 (color 1)
    rw [mul_one] at ht
    have hpos : 0 < (colorFibre π color h (color 1)).card := ht.symm ▸ hbase
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    obtain ⟨hap, hac⟩ : π a = h ∧ color a = color 1 :=
      (Finset.mem_filter.mp ha).2
    simpa [hap] using (hcolor a 1).mp hac
  · intro hh b c
    obtain ⟨g, hg⟩ := hπ h
    have hfix (a : G) : color (g * a) = color a := by
      apply (hcolor (g * a) a).2
      simpa [map_mul, hg, div_eq_mul_inv, mul_assoc] using hh
    have hbij : Function.Bijective (fun a : G => g * a) := by
      refine ⟨fun _ _ he => mul_left_cancel he, ?_⟩
      intro a
      exact ⟨g⁻¹ * a, by simp [mul_assoc]⟩
    symm
    apply Finset.card_bijective (fun a : G => g * a) hbij
    intro a
    simp [colorFibre, map_mul, hg, hfix]

/-- Equality of normalized rank-one labels can be tested without dividing
by their differences. This remains valid when their reductions coincide. -/
theorem normalized_line_generator_rigid {R : Type*} [CommRing R]
    {a b r : R} (h₁ : a = r * b) (h₂ : (1 : R) = r * 1) : a = b := by
  have hr : (1 : R) = r := by simpa using h₂
  simpa [← hr] using h₁

end PrincipalUnitFour.Precision
