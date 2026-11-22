import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace PCTensorConsequences

theorem localized_word {M ι : Type*} [Monoid M] (x y e : M)
    (hxy : x * y = 1) (hyx : y * x = 1) (a b : ι → M)
    (hloc : ∀ i, e * (x * b i * y) = a i * e) (w : List ι) :
    e * (x * (w.map b).prod * y) = (w.map a).prod * e := by
  induction w with
  | nil => simp [hxy]
  | cons i w ih =>
    simp only [List.map_cons, List.prod_cons]
    calc
      e * (x * (b i * (w.map b).prod) * y) =
          (e * (x * b i * y)) * (x * (w.map b).prod * y) := by
            simp [mul_assoc, ← mul_assoc y x, hyx]
      _ = a i * (e * (x * (w.map b).prod * y)) := by rw [hloc, mul_assoc]
      _ = (a i * (w.map a).prod) * e := by rw [ih, mul_assoc]

end PCTensorConsequences
