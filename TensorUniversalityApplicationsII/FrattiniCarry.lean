import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Data.Nat.Basic

namespace FrattiniCarry

/-- The two ways of carrying on adding three representatives agree. -/
theorem carry_assoc (p a b c : ℕ) (hp : 0 < p) :
    (a + b) / p + ((a + b) % p + c) / p =
      (b + c) / p + (a + (b + c) % p) / p := by
  have left : a + b + c = ((a + b) % p + c) + p * ((a + b) / p) := by
    calc
      _ = ((a + b) % p + p * ((a + b) / p)) + c := by rw [Nat.mod_add_div]
      _ = _ := by ac_rfl
  have right : a + b + c = (a + (b + c) % p) + p * ((b + c) / p) := by
    calc
      _ = a + ((b + c) % p + p * ((b + c) / p)) := by rw [Nat.mod_add_div, Nat.add_assoc]
      _ = _ := by ac_rfl
  calc
    _ = (a + b + c) / p := by rw [left, Nat.add_mul_div_left _ _ hp, Nat.add_comm]
    _ = _ := by rw [right, Nat.add_mul_div_left _ _ hp, Nat.add_comm]

/-- A bilinear part of a central factor set is a cocycle. -/
theorem bilinear_cocycle {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    (b : V →+ V →+ W) (x y z : V) :
    b x y + b (x + y) z = b y z + b x (y + z) := by
  simp only [map_add, AddMonoidHom.add_apply]
  exact (add_assoc _ _ _).symm.trans (add_comm _ _)

def extensionMul {V W : Type*} [AddMonoid V] [AddCommMonoid W]
    (factor : V → V → W) (x y : V × W) : V × W :=
  (x.1 + y.1, x.2 + y.2 + factor x.1 y.1)

/-- A central multiplication from a factor set is associative if the cocycle law holds. -/
theorem extensionMul_assoc {V W : Type*} [AddMonoid V] [AddCommMonoid W]
    (factor : V → V → W)
    (cocycle : ∀ u v w, factor u v + factor (u + v) w = factor v w + factor u (v + w))
    (x y z : V × W) :
    extensionMul factor (extensionMul factor x y) z =
      extensionMul factor x (extensionMul factor y z) := by
  apply Prod.ext
  · exact add_assoc _ _ _
  · change (x.2 + y.2 + factor x.1 y.1) + z.2 + factor (x.1 + y.1) z.1 =
      x.2 + (y.2 + z.2 + factor y.1 z.1) + factor x.1 (y.1 + z.1)
    calc
      _ = (x.2 + y.2 + z.2) + (factor x.1 y.1 + factor (x.1 + y.1) z.1) := by ac_rfl
      _ = (x.2 + y.2 + z.2) + (factor y.1 z.1 + factor x.1 (y.1 + z.1)) := by rw [cocycle]
      _ = _ := by ac_rfl

end FrattiniCarry
