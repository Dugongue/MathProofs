import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Bounded powers factor exactly through the image of the cell network. -/

namespace EvenOrdinaryTI.CellPowers

variable {G H X : Type*} [CommGroup G] [CommGroup H] [CommGroup X]

theorem coordinate_power_factors_iff (f : G →* H) (c : G →* X) (h : ℕ) :
    (∀ x, f x = 1 → c x ^ h = 1) ↔
      ∃ χ : f.range →* X, ∀ x, χ (f.rangeRestrict x) = c x ^ h := by
  constructor
  · intro hker
    let p : G →* X := (powMonoidHom h).comp c
    have hp : f.ker ≤ p.ker := by
      intro x hx
      exact MonoidHom.mem_ker.mpr (hker x (MonoidHom.mem_ker.mp hx))
    let e := QuotientGroup.quotientKerEquivRange f
    let χ := (QuotientGroup.lift f.ker p hp).comp e.symm.toMonoidHom
    refine ⟨χ, fun x => ?_⟩
    have hq : e (QuotientGroup.mk x) = f.rangeRestrict x := rfl
    rw [← hq]
    change QuotientGroup.lift f.ker p hp (e.symm (e (QuotientGroup.mk x))) = _
    rw [e.symm_apply_apply, QuotientGroup.lift_mk] <;> rfl
  · rintro ⟨χ, hχ⟩ x hx
    have hr : f.rangeRestrict x = 1 := Subtype.ext hx
    rw [← hχ, hr, map_one]

end EvenOrdinaryTI.CellPowers

#print axioms EvenOrdinaryTI.CellPowers.coordinate_power_factors_iff
