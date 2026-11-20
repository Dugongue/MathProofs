import Mathlib.Algebra.Group.Units.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Prod
import Mathlib.Tactic.Group

namespace RingIsomorphismFibers

theorem normalized_isotopy {R S : Type*} [Monoid R] [Monoid S]
    (a b c : R → S) (u v : Sˣ)
    (hu : a 1 = (u : S)) (hv : b 1 = (v : S))
    (h : ∀ x y, c (x * y) = a x * b y) (x y : R) :
    (↑u⁻¹ : S) * a (x * y) =
      ((↑u⁻¹ : S) * a x) * ((↑u⁻¹ : S) * a y) := by
  have hc (z : R) : c z = a z * (v : S) := by simpa [hv] using h z 1
  have hc' (z : R) : c z = (u : S) * b z := by simpa [hu] using h 1 z
  have hb : b y = ((↑u⁻¹ : S) * a y) * (v : S) := by
    have h' := congrArg (fun z : S => (↑u⁻¹ : S) * z) ((hc' y).symm.trans (hc y))
    simpa [mul_assoc] using h'
  have hm : a (x * y) * (v : S) = a x * b y := (hc (x*y)).symm.trans (h x y)
  rw [hb] at hm
  have hm' := congrArg (fun z : S => z * (↑v⁻¹ : S)) hm
  have hmul : a (x * y) = a x * ((↑u⁻¹ : S) * a y) := by
    simpa [mul_assoc] using hm'
  rw [hmul, mul_assoc]

theorem hub_normalization {U : Type*} [CommGroup U]
    (h₁ h₂ d d₁ d₂ f : U) :
    ((((d / d₁) * h₁) / ((d / d₂) * h₂)) * ((d₁ / d₂) * f)) = (h₁ / h₂) * f := by
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    _ = (d*d⁻¹)*(d₁⁻¹*d₁)*(d₂*d₂⁻¹)*(h₁*h₂⁻¹)*f := by ac_rfl
    _ = _ := by simp

theorem hub_weights_compose {U : Type*} [CommGroup U] (a b c : U) :
    (a / b) * (b / c) = a / c := by
  simp only [div_eq_mul_inv]
  group

def heisenbergMul {R : Type*} [Ring R] (a b : R × R × R) : R × R × R :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2 + a.1 * b.2.1)

def centralChange {R : Type*} [Ring R] (f : (R × R) →+ R) (a : R × R × R) :
    R × R × R :=
  (a.1, a.2.1, a.2.2 + f (a.1, a.2.1))

theorem central_change_mul {R : Type*} [Ring R] (f : (R × R) →+ R)
    (a b : R × R × R) :
    centralChange f (heisenbergMul a b) = heisenbergMul (centralChange f a) (centralChange f b) := by
  rcases a with ⟨x,y,z⟩
  rcases b with ⟨x',y',z'⟩
  change (x + x', y + y', z + z' + x*y' + f ((x,y) + (x',y'))) =
    (x + x', y + y', z + f (x,y) + (z' + f (x',y')) + x*y')
  rw [map_add]
  congr 2
  ac_rfl

end RingIsomorphismFibers

#print axioms RingIsomorphismFibers.normalized_isotopy
#print axioms RingIsomorphismFibers.hub_normalization
#print axioms RingIsomorphismFibers.hub_weights_compose
#print axioms RingIsomorphismFibers.central_change_mul
