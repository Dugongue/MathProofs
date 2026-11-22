import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Abel

theorem extension_lift_torsor {k L M N : Type*} [Field k]
    [AddCommGroup L] [Module k L] [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] (q : M →ₗ[k] N) (f₀ f : L →ₗ[k] M) :
    q.comp f = q.comp f₀ ↔
      ∃! d : L →ₗ[k] q.ker, f = f₀ + q.ker.subtype.comp d := by
  constructor
  · intro h
    have hd (x : L) : (f - f₀) x ∈ q.ker := by
      change q (f x - f₀ x) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun h x)
    let d := (f - f₀).codRestrict q.ker hd
    refine ⟨d, ?_, ?_⟩
    · ext x
      change f x = f₀ x + (f x - f₀ x)
      abel
    · intro e he
      ext x
      change (e x : M) = f x - f₀ x
      have hx := LinearMap.congr_fun he x
      change f x = f₀ x + (e x : M) at hx
      rw [hx]
      abel
  · rintro ⟨d, hd, _⟩
    ext x
    have hx := LinearMap.congr_fun hd x
    change f x = f₀ x + (d x : M) at hx
    change q (f x) = q (f₀ x)
    rw [hx, map_add, show q (d x : M) = 0 from (d x).property, add_zero]
