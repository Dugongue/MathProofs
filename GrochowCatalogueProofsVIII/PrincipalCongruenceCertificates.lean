import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.NoncommRing

namespace GrochowCatalogueEighth

/-- Products in a square-zero layer add all displacements at once. -/
theorem square_zero_list_product {R : Type*} [Ring R] (xs : List R)
    (hz : ∀ x ∈ xs, ∀ y ∈ xs, x * y = 0) :
    (xs.map (fun x => 1 + x)).prod = 1 + xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have htail : ∀ y ∈ xs, ∀ z ∈ xs, y * z = 0 := by
      intro y hy z hz'
      exact hz y (List.mem_cons_of_mem x hy) z (List.mem_cons_of_mem x hz')
    have mulSum (ys : List R) (hyp : ∀ y ∈ ys, x * y = 0) :
        x * ys.sum = 0 := by
      induction ys with
      | nil => simp
      | cons y ys hrec =>
        rw [List.sum_cons, mul_add, hyp y (by simp),
          hrec (fun z hz' => hyp z (List.mem_cons_of_mem y hz')), add_zero]
    have hx : x * xs.sum = 0 :=
      mulSum xs (fun y hy => hz x (by simp) y (List.mem_cons_of_mem x hy))
    rw [List.map_cons, List.prod_cons, List.sum_cons, ih htail]
    calc
      (1 + x) * (1 + xs.sum) = 1 + (x + xs.sum) + x * xs.sum := by noncomm_ring
      _ = 1 + (x + xs.sum) := by rw [hx, add_zero]

/-- Removing a computed prefix by its left inverse preserves the ideal of
    the remaining displacement. The result is stated as the exact identity. -/
theorem left_residual_displacement {R : Type*} [Ring R] (u v a : R)
    (h : a * u = 1) : a * v - 1 = a * (v - u) := by
  rw [mul_sub, h]

end GrochowCatalogueEighth

#print axioms GrochowCatalogueEighth.square_zero_list_product
#print axioms GrochowCatalogueEighth.left_residual_displacement
