
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.SetTheory.Cardinal.Finite

namespace CevaPrecision

variable {G Q H : Type*} [Group G] [Group Q] [Group H]

theorem prescribed_lift_iff (q : G →* Q) (χ : G →* H) (x : G) (δ : H) :
    (∃ y, q y = q x ∧ χ y = δ) ↔ ∃ k ∈ q.ker, χ k = δ / χ x := by
  constructor
  · rintro ⟨y, hq, hχ⟩
    refine ⟨y / x, (q.div_mem_ker_iff).2 hq, ?_⟩
    rw [map_div, hχ]
  · rintro ⟨k, hk, hχ⟩
    refine ⟨k * x, ?_, ?_⟩
    · rw [map_mul, MonoidHom.mem_ker.mp hk, one_mul]
    · rw [map_mul, hχ, div_mul_cancel]

def jointFiberEquiv (q : G →* Q) (χ : G →* H) (x : G) :
    {y : G // q y = q x ∧ χ y = χ x} ≃ {k : G // q k = 1 ∧ χ k = 1} where
  toFun y := ⟨y.val / x, by simp [map_div, y.property.1, y.property.2]⟩
  invFun k := ⟨k.val * x, by simp [map_mul, k.property.1, k.property.2]⟩
  left_inv y := Subtype.ext (div_mul_cancel _ _)
  right_inv k := Subtype.ext (mul_div_cancel_right _ _)

theorem jointFiber_card (q : G →* Q) (χ : G →* H) (x : G) :
    Nat.card {y : G // q y = q x ∧ χ y = χ x} =
      Nat.card {k : G // q k = 1 ∧ χ k = 1} :=
  Nat.card_congr (jointFiberEquiv q χ x)

end CevaPrecision
