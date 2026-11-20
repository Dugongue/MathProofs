import EvenReciprocalRank

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped Matrix
open Matrix Module LinearMap

variable {K I B : Type*} [Field K] [Fintype I] [Fintype B]
variable [DecidableEq I] [DecidableEq B]

/-- The square-label operator used when the reciprocal rows are varied,
while their primal partners are held fixed. -/
def dualSandwich (U M : Matrix I B K) (L : Matrix I I K →ₗ[K] Matrix I I K) :
    Matrix B I K →ₗ[K] Matrix I B K :=
  (mulRightLinearMap I K M).comp (L.comp (mulLeftLinearMap I K U))

theorem dualSandwich_apply (U M : Matrix I B K)
    (L : Matrix I I K →ₗ[K] Matrix I I K) (V : Matrix B I K) :
    dualSandwich U M L V = L (U * V) * M := rfl

theorem dual_sandwich_rank (U M : Matrix I B K)
    (L : Matrix I I K →ₗ[K] Matrix I I K) :
    finrank K L.range ≤ finrank K (dualSandwich U M L).range +
      Fintype.card I * (Fintype.card I - U.rank) +
      Fintype.card I * (Fintype.card I - M.rank) := by
  have h₁ := precompose_rank_loss (mulLeftLinearMap I K U) L
  have h₂ := postcompose_rank_loss (L.comp (mulLeftLinearMap I K U))
    (mulRightLinearMap I K M)
  rw [mulLeft_finrank_range, finrank_matrix, Module.finrank_self, mul_one,
    ← Nat.mul_sub_left_distrib] at h₁
  have hk : finrank K (mulRightLinearMap I K M).ker =
      Fintype.card I * (Fintype.card I - M.rank) := by
    have hh := (mulRightLinearMap I K M).finrank_range_add_finrank_ker
    rw [mulRight_finrank_range, finrank_matrix, Module.finrank_self, mul_one] at hh
    rw [Nat.mul_sub_left_distrib]
    omega
  rw [hk] at h₂
  change _ ≤ finrank K
    ((mulRightLinearMap I K M).comp (L.comp (mulLeftLinearMap I K U))).range + _ + _
  omega

#print axioms dual_sandwich_rank

end Mathproof.EvenTI.Reciprocal.Four
