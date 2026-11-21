import Mathlib.Algebra.Group.Basic
import Lean.Elab.Tactic.Omega

namespace SymplecticOrientation

theorem even_exponent_disappears {G : Type*} [Group G] (u : G)
    (hu : u ^ (2 : ℕ) = 1) (k : ℕ) : u ^ (2 * k) = 1 := by
  rw [pow_mul, hu, one_pow]

theorem odd_multiplicity_cancellation {G : Type*} [Group G] (u : G)
    (hu : u ^ (2 : ℕ) = 1) (a b : ℕ) :
    u ^ (2 * a + (2 * b + 1) - 1) = 1 := by
  have h : 2 * a + (2 * b + 1) - 1 = 2 * (a + b) := by omega
  rw [h, even_exponent_disappears u hu]

theorem common_scalar_rescaling {G : Type*} [CommGroup G] (u s : G)
    (hs : s ^ (2 : ℕ) = 1) : s ^ (2 : ℕ) * u = u := by
  rw [hs, one_mul]

end SymplecticOrientation
