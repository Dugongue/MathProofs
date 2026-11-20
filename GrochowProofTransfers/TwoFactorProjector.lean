import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

/-!
# Two eigenvalue families in a linear matrix family

A scalar collision along the common-value hyperplane and a square-free
annihilator at a separating evaluation give a constant idempotent decomposition.
Specializing the target algebra to endomorphisms gives a common decomposition
of every matrix in the family by the image and kernel of that idempotent.
-/

namespace GrochowTransfer

variable {K V R : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Ring R] [Algebra K R]

theorem twoFactors_projector (B : V →ₗ[K] R) (a b : V →ₗ[K] K) (v : V)
    (hv : a v - b v = 1)
    (hcollision : ∀ x, a x = b x → B x = b x • (1 : R))
    (hsemisimple : (B v - b v • (1 : R)) * (B v - a v • (1 : R)) = 0) :
    ∃ P : R, P * P = P ∧ ∀ x, B x = (a x - b x) • P + b x • (1 : R) := by
  let C := B - b.smulRight (1 : R)
  let d := a - b
  have hdv : d v = 1 := hv
  have hconst (x : V) : C x = (a x - b x) • C v := by
    let y := x - d x • v
    have hdy : d y = 0 := by simp [y, hdv]
    have hEq : a y = b y := sub_eq_zero.mp hdy
    have hzero : C y = 0 := sub_eq_zero.mpr (hcollision y hEq)
    change C (x - d x • v) = 0 at hzero
    rw [map_sub, map_smul] at hzero
    exact sub_eq_zero.mp hzero
  refine ⟨C v, ?_, ?_⟩
  · have hshift : B v - a v • (1 : R) = C v - 1 := by
      change B v - a v • (1 : R) = (B v - b v • (1 : R)) - 1
      have hd : a v • (1 : R) - b v • (1 : R) = 1 := by
        rw [← sub_smul, hv, one_smul]
      have heq : a v • (1 : R) = b v • (1 : R) + 1 := by
        simpa [add_comm] using (sub_eq_iff_eq_add.mp hd)
      rw [heq]
      abel
    rw [hshift] at hsemisimple
    change C v * (C v - 1) = 0 at hsemisimple
    rw [mul_sub, mul_one] at hsemisimple
    exact sub_eq_zero.mp hsemisimple
  · intro x
    have hx : B x - b x • (1 : R) = (a x - b x) • C v := hconst x
    exact sub_eq_iff_eq_add.mp hx

end GrochowTransfer
