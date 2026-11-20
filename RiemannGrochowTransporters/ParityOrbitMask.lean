import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Set.Lattice

namespace ParityOrbitMask

variable {G X R Y : Type*} [Group G] [MulAction G X]

def view (render : R → Y) (tag : R → Bool) (a b : X) (sample : R × G) : Y × X :=
  (render sample.1, sample.2 • if tag sample.1 then b else a)

private def shift (tag : R → Bool) (g : G) : R × G ≃ R × G where
  toFun s := (s.1, s.2 * if tag s.1 then g else g⁻¹)
  invFun s := (s.1, s.2 * if tag s.1 then g⁻¹ else g)
  left_inv s := by
    rcases s with ⟨r, h⟩
    cases htag : tag r <;> simp [htag, mul_assoc]
  right_inv s := by
    rcases s with ⟨r, h⟩
    cases htag : tag r <;> simp [htag, mul_assoc]

/-- A mask on one common orbit couples the two parity-conditioned views. -/
theorem parity_views_match (render : R → Y) (tag : R → Bool) (a : X) (g : G) :
    ∃ e : R × G ≃ R × G, ∀ s,
      view render tag a (g • a) s = view render tag (g • a) a (e s) := by
  refine ⟨shift tag g, ?_⟩
  rintro ⟨r, h⟩
  cases htag : tag r <;> simp [view, shift, htag, mul_smul]

/-- Once the other views determine their parity, a disjoint last orbit separates the views. -/
theorem parity_views_disjoint (render : R → Y) (tag : R → Bool) (a b : X)
    (hTag : ∀ r t, render r = render t → tag r = tag t)
    (hOrbit : ∀ g h : G, g • a ≠ h • b) :
    Disjoint (Set.range (view (G := G) render tag a b))
      (Set.range (view (G := G) render tag b a)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨⟨r, g⟩, rfl⟩ ⟨⟨t, h⟩, hw⟩
  have htag := hTag t r (congrArg Prod.fst hw)
  have hs := congrArg Prod.snd hw
  change (h • (if tag t then a else b)) = g • (if tag r then b else a) at hs
  rw [htag] at hs
  cases hrt : tag r with
  | false => exact hOrbit g h (by simpa [hrt] using hs.symm)
  | true => exact hOrbit h g (by simpa [hrt] using hs)

end ParityOrbitMask
