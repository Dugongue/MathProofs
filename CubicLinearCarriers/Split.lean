import Mathlib.Algebra.CharP.Frobenius
import Mathlib.LinearAlgebra.Projection

open scoped BigOperators

namespace CubicLinearCarriers

theorem compare_on_blocks {K V ι : Type*} [Field K] [CharP K 3]
    [AddCommGroup V] [Module K V] [Fintype ι]
    (p : ι → V →ₗ[K] V) (cover : ∀ x, ∑ i, p i x = x)
    (f g : V → K) (l : V →ₗ[K] K)
    (delta : ∀ x, f x - g x = (l x) ^ 3)
    (blocks : ∀ x, (∑ i, f (p i x)) = ∑ i, g (p i x)) : f = g := by
  funext x
  apply sub_eq_zero.mp
  calc
    f x - g x = (frobenius K 3) (l x) := by exact delta x
    _ = (frobenius K 3) (l (∑ i, p i x)) := by rw [cover x]
    _ = ∑ i, (frobenius K 3) (l (p i x)) := by rw [map_sum, map_sum]
    _ = ∑ i, (f (p i x) - g (p i x)) := by
      exact Finset.sum_congr rfl (fun i _ => (delta (p i x)).symm)
    _ = 0 := by rw [Finset.sum_sub_distrib, blocks, sub_self]

end CubicLinearCarriers
