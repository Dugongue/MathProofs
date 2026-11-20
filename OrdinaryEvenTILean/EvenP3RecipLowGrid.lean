import EvenNextRecipGrid

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped BigOperators
open Module LinearMap Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

variable {K J W V : Type*} [Field K] [Fintype J] [DecidableEq J]
variable [AddCommGroup W] [Module K W] [Module.Finite K W]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

set_option backward.isDefEq.respectTransparency false in
/-- The paired grid only needs to cover each block modulo the radical.
The range-restricted form represents the quotient without choosing coordinates. -/
theorem rank_of_grid_and_radical_quotient
    (B : LinearMap.BilinForm K W) (hs : ∀ x y, B x y = B y x)
    (D : V →ₗ[K] Grid J W)
    (hD : Function.Surjective ((LinearMap.compLeft B.rangeRestrict (J × J)).comp D)) :
    (Fintype.card J ^ 2 - 1) * finrank K B.range ≤
      finrank K ((gridForm B + B.compl₁₂ (diagFold (J := J)) diagFold).compl₁₂ D D).range := by
  let q := LinearMap.compLeft B.rangeRestrict (J × J)
  let : Module.Free K (Grid J B.range) :=
    Module.Free.of_divisionRing K (Grid J (↥B.range))
  obtain ⟨R, hR⟩ := (q.comp D).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hD)
  let T := R.comp q
  have hp (x : Grid J W) (j : J × J) : B (D (T x) j) = B (x j) := by
    have h := congrFun (LinearMap.congr_fun hR (q x)) j
    exact congrArg Subtype.val h
  have hd (x : Grid J W) : B (diagFold (K := K) (D (T x))) = B (diagFold (K := K) x) := by
    change B (∑ j : J, D (T x) (j,j)) = B (∑ j : J, x (j,j))
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j _ => hp x (j,j))
  let F := gridForm B + B.compl₁₂ (diagFold (J := J)) diagFold
  have hF : (F.compl₁₂ D D).compl₁₂ T T = F := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change gridForm B (D (T x)) (D (T y)) + B (diagFold (D (T x))) (diagFold (D (T y))) =
      gridForm B x y + B (diagFold x) (diagFold y)
    rw [gridForm_apply, gridForm_apply, hd, hs (diagFold x), hd, hs (diagFold y)]
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    rw [hp, hs (x p), hp, hs (y p.swap)]
  have h := rank_pullback_le (F.compl₁₂ D D) T
  rw [hF] at h
  exact (rank_of_grid_and_sum B).trans h

#print axioms rank_of_grid_and_radical_quotient

end Mathproof.EvenTI.Reciprocal.SquareLow
