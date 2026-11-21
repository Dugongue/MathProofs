import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units.Basic

namespace ConductorGenus

/-- A bilinear-product transporter normalizes to a common multiplicative map. -/
theorem normalize_autotopy {R : Type*} [CommMonoid R]
    (a b c : R → R) (u v : Rˣ) (hu : a 1 = ↑u) (hv : b 1 = ↑v)
    (h : ∀ x y, c (x * y) = a x * b y) :
    ∃ f : R →* R, (∀ x, a x = ↑u * f x) ∧
      (∀ x, b x = ↑v * f x) ∧ (∀ x, c x = ↑u * ↑v * f x) := by
  have hc_a (x : R) : c x = a x * ↑v := by simpa [hv] using h x 1
  have hc_b (x : R) : c x = ↑u * b x := by simpa [hu] using h 1 x
  let f₀ (x : R) : R := (↑(u⁻¹) : R) * a x
  have ha (x : R) : a x = ↑u * f₀ x := by simp [f₀, ← mul_assoc]
  have hb (x : R) : b x = ↑v * f₀ x := by
    calc
      b x = (↑(u⁻¹) : R) * (↑u * b x) := by simp [← mul_assoc]
      _ = (↑(u⁻¹) : R) * (a x * ↑v) := by rw [← hc_b, hc_a]
      _ = ↑v * f₀ x := by simp [f₀, mul_assoc, mul_comm]
  have hc (x : R) : c x = (↑u * ↑v) * f₀ x := by
    rw [hc_b, hb]
    exact (mul_assoc _ _ _).symm
  have hf (x y : R) : f₀ (x * y) = f₀ x * f₀ y := by
    have eqn := h x y
    rw [hc, ha, hb] at eqn
    have eqn' : (↑(u * v) : R) * f₀ (x * y) =
        (↑(u * v) : R) * (f₀ x * f₀ y) := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using eqn
    have scaled := congrArg (fun z : R => (↑((u * v)⁻¹) : R) * z) eqn'
    simpa [← mul_assoc] using scaled
  exact ⟨{ toFun := f₀, map_one' := by simp [f₀, hu], map_mul' := hf }, ha, hb, hc⟩

end ConductorGenus
