import Mathlib.Algebra.BigOperators.Group.List.Basic
import Lean.Elab.Tactic.Omega

namespace RecursiveDeterminants

theorem square_character_even {G : Type*} [Group G] (u : G)
    (hu : u ^ (2 : ℕ) = 1) (k : ℕ) :
    u ^ ((2 * k + 1) + 1) = 1 ∧ u ^ ((2 * k + 1) - 1) = 1 := by
  have hp : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
  have hm : (2 * k + 1) - 1 = 2 * k := by omega
  rw [hp, hm, pow_mul, pow_mul, hu, one_pow, one_pow]
  exact ⟨rfl, rfl⟩

theorem odd_multiplier_cancels {G : Type*} [Group G] (u : G)
    (hu : u ^ (2 : ℕ) = 1) (k l : ℕ) :
    u ^ ((2 * k + 1) + (2 * l + 1)) = 1 := by
  have h : (2 * k + 1) + (2 * l + 1) = 2 * (k + l + 1) := by omega
  rw [h, pow_mul, hu, one_pow]

theorem telescoping_calibration {G : Type*} [CommGroup G] :
    ∀ (steps : List (G × G)) (v : G),
      (steps.map fun p => p.1⁻¹ * p.2).prod * v =
        (steps.map Prod.fst).prod⁻¹ * ((steps.map Prod.snd).prod * v) := by
  intro steps
  induction steps with
  | nil => intro v; simp
  | cons p steps ih =>
    intro v
    simp only [List.map_cons, List.prod_cons, mul_inv_rev]
    rw [mul_assoc, ih]
    ac_rfl

end RecursiveDeterminants
