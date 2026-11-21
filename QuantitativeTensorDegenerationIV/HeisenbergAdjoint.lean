import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Group.Units.Basic

namespace HeisenbergAdjoint

theorem diagonal_slot {R : Type*} [Ring R] (f g : R → R)
    (h : ∀ x y, f x * y = x * g y) :
    (∀ x, f x = x * f 1) ∧ (∀ y, g y = f 1 * y) := by
  have hg y : g y = f 1 * y := by simpa using (h 1 y).symm
  exact ⟨fun x => by simpa [hg 1] using h x 1, hg⟩

theorem left_offdiagonal_zero {R : Type*} [Ring R] (f g : R → R)
    (u v : R) (hu : IsUnit (u * v - v * u))
    (h : ∀ x y, f x * y = -(g y * x)) :
    (∀ x, f x = 0) ∧ (∀ y, g y = 0) := by
  let a := f 1
  have hg y : g y = -(a * y) := by
    have hy : a * y = -g y := by simpa [a] using h 1 y
    simpa using (congrArg Neg.neg hy).symm
  have hf x : f x = a * x := by
    simpa [hg 1] using h x 1
  have hcomm : a * (u * v - v * u) = 0 := by
    have huv : a * (u * v) = a * (v * u) := by
      simpa [hf u, hg v, mul_assoc] using h u v
    rw [mul_sub, huv, sub_self]
  obtain ⟨s, hs⟩ := hu
  have hz : a * (s : R) = 0 := hs.symm ▸ hcomm
  have ha : a = 0 := calc
    a = a * ((s : R) * (↑s⁻¹ : R)) := by simp
    _ = (a * (s : R)) * (↑s⁻¹ : R) := by rw [mul_assoc]
    _ = 0 := by simp [hz]
  exact ⟨fun x => by simp [hf x, ha], fun y => by simp [hg y, ha]⟩

theorem right_offdiagonal_zero {R : Type*} [Ring R] (f g : R → R)
    (u v : R) (hu : IsUnit (u * v - v * u))
    (h : ∀ x y, y * f x = -(x * g y)) :
    (∀ x, f x = 0) ∧ (∀ y, g y = 0) := by
  let a := f 1
  have hg y : g y = -(y * a) := by
    have hy : y * a = -g y := by simpa [a] using h 1 y
    simpa using (congrArg Neg.neg hy).symm
  have hf x : f x = x * a := by
    simpa [hg 1] using h x 1
  have hcomm : (u * v - v * u) * a = 0 := by
    have huv : (u * v) * a = (v * u) * a := by
      simpa [hf v, hg u, mul_assoc] using h v u
    rw [sub_mul, huv, sub_self]
  obtain ⟨s, hs⟩ := hu
  have hz : (s : R) * a = 0 := hs.symm ▸ hcomm
  have ha : a = 0 := calc
    a = ((↑s⁻¹ : R) * (s : R)) * a := by simp
    _ = (↑s⁻¹ : R) * ((s : R) * a) := by rw [mul_assoc]
    _ = 0 := by simp [hz]
  exact ⟨fun x => by simp [hf x, ha], fun y => by simp [hg y, ha]⟩

end HeisenbergAdjoint
