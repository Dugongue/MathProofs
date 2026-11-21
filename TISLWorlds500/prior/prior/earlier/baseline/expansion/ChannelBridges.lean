import Mathlib.Algebra.Group.Defs

namespace TISLAtlas200

theorem complementary_channels {R : Type*} [AddMonoid R]
    (b : Bool) (x p q : R) (hs : x = p + q)
    (hp : b = false → p = 0) (hq : b = true → q = 0) :
    p = (if b then x else 0) ∧ q = (if b then 0 else x) := by
  cases b with
  | false =>
    have hp0 := hp rfl
    exact ⟨by simpa using hp0, by simpa [hp0] using hs.symm⟩
  | true =>
    have hq0 := hq rfl
    exact ⟨by simpa [hq0] using hs.symm, by simpa using hq0⟩

theorem trajectory_unique {S : Type*} (f : ℕ → S → S) (a b : ℕ → S)
    (h0 : a 0 = b 0) (ha : ∀ i, a (i + 1) = f i (a i))
    (hb : ∀ i, b (i + 1) = f i (b i)) : a = b := by
  funext i
  induction i with
  | zero => exact h0
  | succ i hi =>
    rw [ha i, hb i, hi]

end TISLAtlas200
