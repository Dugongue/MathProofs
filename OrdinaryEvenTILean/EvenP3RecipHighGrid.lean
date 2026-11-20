import EvenP3RecipHighCross

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

noncomputable section

variable {K X C R M : Type*} [Field K] [AddCommGroup X] [Module K X]
variable [Module.Finite K X] [AddCommGroup M] [Module K M] [Module.Finite K M]
variable [Fintype C] [Fintype R] [DecidableEq C] [DecidableEq R]

theorem grid_rank_of_cross_groups (f : C ⊕ R → X →ₗ[K] M)
    (B : LinearMap.BilinForm K M)
    (h : ∀ y : C → X,
      (∀ (t : R) (x : X), (∑ u : C, B (f (.inr t) (y u)) (f (.inl u) x)) = 0) →
      y = 0) :
    finrank K (C → X) ≤
      finrank K ((gridForm B).compl₁₂ (evaluatedGrid f) (evaluatedGrid f)).range := by
  apply rank_ge_of_cross_kernel _ (colInclude (K := K) (R := R)) (rowInclude (K := K) (C := C))
  intro y hy
  apply h y
  intro t x
  have hz := hy (Pi.single t x)
  change gridForm B (evaluatedGrid f (colInclude (K := K) (R := R) y))
    (evaluatedGrid f (rowInclude (K := K) (C := C) (Pi.single t x))) = 0 at hz
  rw [grid_cross_eval] at hz
  have he (u : C) :
      (∑ b : R, B (f (.inr b) (y u)) (f (.inl u) ((Pi.single t x : R → X) b))) =
        B (f (.inr t) (y u)) (f (.inl u) x) := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  simpa only [he] using hz

theorem corrected_grid_rank_of_cross_groups (f : C ⊕ R → X →ₗ[K] M)
    (B : LinearMap.BilinForm K M)
    (h : ∀ y : C → X,
      (∀ (t : R) (x : X), (∑ u : C, B (f (.inr t) (y u)) (f (.inl u) x)) = 0) →
      y = 0) :
    finrank K (C → X) - finrank K B.range ≤
      finrank K ((gridForm B + B.compl₁₂ diagFold diagFold).compl₁₂
        (evaluatedGrid f) (evaluatedGrid f)).range := by
  let D := evaluatedGrid f
  let F := (gridForm B).compl₁₂ D D
  let G := B.compl₁₂ (diagFold.comp D) (diagFold.comp D)
  have hf : finrank K (C → X) ≤ finrank K F.range :=
    grid_rank_of_cross_groups f B h
  have hg : finrank K G.range ≤ finrank K B.range :=
    rank_pullback_le B (diagFold.comp D)
  have hab := correction_rank_lower F G
  have hb : finrank K (C → X) - finrank K B.range ≤ finrank K F.range - finrank K G.range := by
    omega
  exact hb.trans hab

#print axioms grid_rank_of_cross_groups
#print axioms corrected_grid_rank_of_cross_groups

end
end Mathproof.EvenTI.Reciprocal.Four
