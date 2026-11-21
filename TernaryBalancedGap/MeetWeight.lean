import Mathlib.Algebra.Group.Action.Basic

theorem meet_weight {G X S : Type*} [Group G] [Monoid S] [MulAction G X]
    (weight : G →* S) (p q : G) (x y : X) (v : S)
    (matched : p • x = q • y)
    (free : ∀ a b : G, a • x = b • x → a = b) :
    (∃ g : G, g • x = y ∧ weight g = v) ↔ weight (q⁻¹) * weight p = v := by
  have h : (q⁻¹ * p) • x = y := by rw [mul_smul, matched, inv_smul_smul]
  constructor
  · rintro ⟨g, hg, hw⟩
    have eqn := free g (q⁻¹ * p) (hg.trans h.symm)
    simpa only [eqn, map_mul] using hw
  · intro hw
    exact ⟨_, h, by simpa only [map_mul] using hw⟩
