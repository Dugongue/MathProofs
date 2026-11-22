import Mathlib

namespace CevaFour.Segre

/-- The projective ratio between a grid coordinate and its origin separates. -/
theorem grid_ratio {G : Type*} [CommGroup G] (x y x₀ y₀ : G) :
    (x * y) / (x₀ * y₀) = (x / x₀) * (y / y₀) := by
  rw [div_mul_div_comm]

/-- A pinned pair of Segre axes implements a multiplication register. -/
theorem grid_gate {G : Type*} [CommGroup G] (xᵢ xⱼ xₖ x₀ yⱼ y₀ : G)
    (tie : yⱼ / y₀ = xⱼ / x₀) :
    xᵢ * yⱼ = xₖ * y₀ ↔ xₖ / x₀ = (xᵢ / x₀) * (xⱼ / x₀) := by
  have left : (xᵢ * yⱼ) / (x₀ * y₀) = (xᵢ / x₀) * (xⱼ / x₀) := by
    rw [grid_ratio, tie]
  have right : (xₖ * y₀) / (x₀ * y₀) = xₖ / x₀ := by
    rw [grid_ratio, div_self', mul_one]
  constructor
  · intro h
    exact right.symm.trans ((congrArg (fun a : G => a / (x₀ * y₀)) h).symm.trans left)
  · intro h
    apply (div_left_injective (b := x₀ * y₀))
    exact left.trans (h.symm.trans right.symm)

end CevaFour.Segre
