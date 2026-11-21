import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Module.Submodule.Ker

namespace CharacteristicTwoCubic

theorem isotropic_projection_must_vanish (x y l k : ℕ)
    (hxy : l ≤ x + y) (hx : 9 * x ≤ k) (hy : 9 * y ≤ k)
    (hk : k ≤ l) : l = 0 := by omega

theorem intersection_from_disjoint_projections {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p : V →ₗ[K] W) (Y S T : Submodule K V) (L1 L2 : Submodule K W)
    (hY : Y = LinearMap.ker p) (hYS : Y ≤ S) (hYT : Y ≤ T)
    (hS : ∀ x ∈ S, p x ∈ L1) (hT : ∀ x ∈ T, p x ∈ L2)
    (hd : Disjoint L1 L2) : S ⊓ T = Y := by
  apply le_antisymm _ (le_inf hYS hYT)
  intro x hx
  have hmem : p x ∈ L1 ⊓ L2 := ⟨hS x hx.1, hT x hx.2⟩
  have hp : p x = 0 := by
    simpa [hd.eq_bot] using hmem
  rw [hY]
  exact hp

theorem trace_commutator_pairing {R S : Type*} [Ring R] [AddCommGroup S]
    (tr : R →+ S) (cyclic : ∀ a b, tr (a * b) = tr (b * a)) (h a b : R) :
    tr (h * (a * b - b * a)) = tr ((h * a - a * h) * b) := by
  have h1 : tr (h * (a * b)) = tr ((h * a) * b) := by rw [mul_assoc]
  have h2 : tr (h * (b * a)) = tr ((a * h) * b) := calc
    tr (h * (b * a)) = tr ((h * b) * a) := by rw [mul_assoc]
    _ = tr (a * (h * b)) := cyclic _ _
    _ = tr ((a * h) * b) := by rw [mul_assoc]
  rw [mul_sub, sub_mul, map_sub, map_sub, h1, h2]

end CharacteristicTwoCubic
