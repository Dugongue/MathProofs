import Mathlib.Tactic

namespace AffineConjugacyAdvances

theorem innerOfCayleyMarker {G : Type*} [Group G] (alpha : G ≃* G) (sigma : G → G)
    (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hact : ∀ g x, sigma (g * x) = alpha g * sigma x)
    (hmark : ∀ s ∈ S, sigma s = sigma 1 * s) :
    ∀ g, alpha g = sigma 1 * g * (sigma 1)⁻¹ := by
  let c : G ≃* G := MulAut.conj (sigma 1)
  let D : Subgroup G := alpha.toMonoidHom.eqLocus c.toMonoidHom
  have hSD : S ⊆ D := by
    intro s hs
    change alpha s = c s
    change alpha s = sigma 1 * s * (sigma 1)⁻¹
    have he : alpha s * sigma 1 = sigma 1 * s := by
      rw [← hact s 1, mul_one, hmark s hs]
    calc
      alpha s = (alpha s * sigma 1) * (sigma 1)⁻¹ := by group
      _ = _ := by rw [he]
  have hD := (Subgroup.closure_le D).2 hSD
  rw [hgen] at hD
  intro g
  have hg : g ∈ D := hD (show g ∈ (⊤ : Subgroup G) by trivial)
  exact hg

theorem graphConjugation {G : Type*} [Group G] (u v a b : G)
    (h : u * a * u⁻¹ = v * b * v⁻¹) :
    a = (u⁻¹ * v) * b * (u⁻¹ * v)⁻¹ := by
  calc
    a = u⁻¹ * (u * a * u⁻¹) * u := by group
    _ = u⁻¹ * (v * b * v⁻¹) * u := by rw [h]
    _ = _ := by group

theorem terminalNormalization {P U : Type*} [Group P] [Group U]
    (f : P →* U) (s : U →* P) (hr : ∀ a, f (s a) = a)
    (hc : ∀ a x, Commute (s a) x) (x y : P) :
    f ((s (f x))⁻¹ * x) = 1 ∧
    (s (f (x * y)))⁻¹ * (x * y) =
      ((s (f x))⁻¹ * x) * ((s (f y))⁻¹ * y) := by
  constructor
  · simp only [map_mul, map_inv, hr, inv_mul_cancel]
  · simp only [map_mul, mul_inv_rev]
    have hswap : Commute (s (f y))⁻¹ ((s (f x))⁻¹ * x) :=
      (hc (f y) _).inv_left
    calc
      _ = ((s (f y))⁻¹ * ((s (f x))⁻¹ * x)) * y := by simp only [mul_assoc]
      _ = _ := by rw [hswap.eq, mul_assoc]

end AffineConjugacyAdvances
