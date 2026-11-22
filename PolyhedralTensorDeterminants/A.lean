import Mathlib

namespace PolyhedraFour.Triangle

/-- The unit-coordinate form of Ceva uses only the group
of invertible side ratios. -/
theorem ceva_ratios {G : Type*} [CommGroup G] (p q r : G) :
    (∃ x y z : G, p = x / y ∧ q = y / z ∧ r = z / x) ↔ p * q * r = 1 := by
  constructor
  · rintro ⟨x, y, z, rfl, rfl, rfl⟩
    simp only [div_eq_mul_inv]
    group
  · intro h
    refine ⟨p * q, q, 1, ?_, by simp, ?_⟩
    · simp
    · calc
        r = (p * q)⁻¹ * (p * q * r) := by group
        _ = 1 / (p * q) := by rw [h]; simp

/-- Character whose exponents, indexed by the triangle vertices, are (1,1,-2). -/
def character {G : Type*} [CommGroup G] (x y z : G) := x * y / (z * z)

/-- Ratio freedom on any two sides already gives every nontrivial target,
provided squares are surjective. One side alone gives no such target. -/
theorem triangle_majority_character {G : Type*} [CommGroup G] (δ : G) (hδ : δ ≠ 1)
    (square_surjective : ∀ g : G, ∃ x : G, x * x = g) (A B C : Prop) :
    (∃ x y z : G, (¬ A → x = y) ∧ (¬ B → y = z) ∧ (¬ C → z = x) ∧
      character x y z = δ) ↔ (A ∧ B) ∨ (B ∧ C) ∨ (C ∧ A) := by
  classical
  constructor
  · rintro ⟨x, y, z, hA, hB, hC, hδ'⟩
    by_contra h
    have hxy : x = y := by
      by_cases ha : A
      · have hb : ¬ B := fun hb => h (Or.inl ⟨ha, hb⟩)
        have hc : ¬ C := fun hc => h (Or.inr (Or.inr ⟨hc, ha⟩))
        exact ((hB hb).trans (hC hc)).symm
      · exact hA ha
    have hyz : y = z := by
      by_cases hb : B
      · have ha : ¬ A := fun ha => h (Or.inl ⟨ha, hb⟩)
        have hc : ¬ C := fun hc => h (Or.inr (Or.inl ⟨hb, hc⟩))
        exact (hA ha).symm.trans (hC hc).symm
      · exact hB hb
    apply hδ
    rw [hxy, hyz] at hδ'
    simpa [character] using hδ'.symm
  · rintro (⟨ha, hb⟩ | ⟨hb, hc⟩ | ⟨hc, ha⟩)
    · exact ⟨1, δ, 1, fun hn => (hn ha).elim, fun hn => (hn hb).elim,
        fun _ => rfl, by simp [character]⟩
    · obtain ⟨root, hroot⟩ := square_surjective δ
      exact ⟨root, root, 1, fun _ => rfl, fun hn => (hn hb).elim,
        fun hn => (hn hc).elim, by simpa [character] using hroot⟩
    · exact ⟨δ, 1, 1, fun hn => (hn ha).elim, fun _ => rfl,
        fun hn => (hn hc).elim, by simp [character]⟩

end PolyhedraFour.Triangle
