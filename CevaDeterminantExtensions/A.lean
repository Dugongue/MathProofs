import Mathlib

namespace CevaFour.Count

/-- A scale at the root and one independent subgroup phase at every other
component give exactly the admissible component scales. -/
theorem card_component_scales {C G : Type*} [Finite C] [Group G] [Finite G]
    (root : C) (Γ : Subgroup G) :
    Nat.card {x : C → G // ∀ c, (x root)⁻¹ * x c ∈ Γ} =
      Nat.card G * (Nat.card Γ) ^ (Nat.card C - 1) := by
  classical
  let e : {x : C → G // ∀ c, (x root)⁻¹ * x c ∈ Γ} ≃
      G × ({c : C // c ≠ root} → Γ) := {
    toFun := fun x =>
      (x.1 root, fun c => ⟨(x.1 root)⁻¹ * x.1 c, x.2 c⟩)
    invFun := fun q => ⟨
      (fun c => if h : c = root then q.1 else q.1 * (q.2 ⟨c, h⟩ : G)), by
        intro c
        by_cases h : c = root
        · subst c
          simpa using Γ.one_mem
        · simpa [h] using (q.2 ⟨c, h⟩).property⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext c
      by_cases h : c = root
      · subst c
        simp
      · simp [h]
    right_inv := by
      intro q
      apply Prod.ext
      · simp
      · funext c
        apply Subtype.ext
        simp [c.property] }
  have hcard : Nat.card {c : C // c ≠ root} = Nat.card C - 1 := by
    letI := Fintype.ofFinite C
    letI := Fintype.ofFinite {c : C // c ≠ root}
    letI := Fintype.ofFinite {c : C // c = root}
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun c : C => c = root), Fintype.card_subtype_eq]
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun, hcard]

/-- Fixing a scaled perfect pairing leaves one freely chosen scalar in the two
standard semilinear arrow maps. -/
theorem card_scaled_pair {G : Type*} [Group G] [Finite G] (t : G) :
    Nat.card {p : G × G // p.1 * p.2 = t} = Nat.card G := by
  apply Nat.card_congr
  refine {
    toFun := fun p => p.1.1
    invFun := fun x => ⟨(x, x⁻¹ * t), by simp⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  rintro ⟨⟨x, y⟩, h⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change x⁻¹ * t = y
    change x * y = t at h
    rw [← h]
    simp

end CevaFour.Count
