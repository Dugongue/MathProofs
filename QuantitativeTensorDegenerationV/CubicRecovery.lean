import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Group.Units.Basic

namespace CubicRecovery

theorem maximal_hessian_kernel {U V S : Type*} [Zero U] [Zero V] [AddZeroClass S]
    (c : U → V) (a : U → U → S) (pair : V → S)
    (hp : pair 0 = 0)
    (hn : ∀ x, c x = 0 → (∀ y, c y = 0 → a x y = 0) → x = 0)
    {x : U} (hx : c x = 0) (hh : ∀ y, a x y + pair (c y) = 0) :
    x = 0 := by
  refine hn x hx ?_
  intro y hy
  simpa [hy, hp] using hh y

theorem three_matrix_crosses_intersect_trivially {R : Type*} [Zero R]
    (A : ℕ → ℕ → R)
    (h : ∀ i j p, p < 3 → i ≠ p → j ≠ p → A i j = 0) :
    ∀ i j, A i j = 0 := by
  intro i j
  by_contra hn
  have h0 : i = 0 ∨ j = 0 := by
    by_contra hh
    exact hn (h i j 0 (by decide) (fun hi => hh (Or.inl hi)) (fun hj => hh (Or.inr hj)))
  have h1 : i = 1 ∨ j = 1 := by
    by_contra hh
    exact hn (h i j 1 (by decide) (fun hi => hh (Or.inl hi)) (fun hj => hh (Or.inr hj)))
  have h2 : i = 2 ∨ j = 2 := by
    by_contra hh
    exact hn (h i j 2 (by decide) (fun hi => hh (Or.inl hi)) (fun hj => hh (Or.inr hj)))
  omega

theorem symmetric_offdiagonal_zero {R : Type*} [Ring R] (f g : R → R)
    (u v : R) (hu : IsUnit (u * v - v * u))
    (h : ∀ x y, f x * y = g y * x) :
    (∀ x, f x = 0) ∧ (∀ y, g y = 0) := by
  let a := f 1
  have hg y : g y = a * y := by simpa [a] using (h 1 y).symm
  have hf x : f x = a * x := by simpa [hg 1] using h x 1
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

end CubicRecovery
