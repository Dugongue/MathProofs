import EvenNextRecipHighOrder

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

noncomputable section

variable {K V W W' : Type*} [Field K]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]
variable [AddCommGroup W] [Module K W]
variable [AddCommGroup W'] [Module K W']

/-- Restricting the two sides of a bilinear form can only decrease rank. -/
theorem rank_cross_le (F : LinearMap.BilinForm K V)
    (left : W →ₗ[K] V) (right : W' →ₗ[K] V) :
    finrank K ((right.dualMap).comp (LinearMap.comp F left)).range ≤ finrank K F.range := by
  rw [LinearMap.range_comp]
  exact (Submodule.finrank_map_le _ _).trans
    (Submodule.finrank_mono (LinearMap.range_comp_le_range left F))

private theorem finrank_range_add_le (F G : LinearMap.BilinForm K V) :
    finrank K (F+G).range ≤ finrank K F.range + finrank K G.range := by
  have h : (F+G).range ≤ F.range ⊔ G.range := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.mpr ⟨F x, ⟨x,rfl⟩, G x, ⟨x,rfl⟩, rfl⟩
  exact (Submodule.finrank_mono h).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem correction_rank_lower (F G : LinearMap.BilinForm K V) :
    finrank K F.range - finrank K G.range ≤ finrank K (F+G).range := by
  have h := finrank_range_add_le (F+G) (-G)
  rw [show F + G + -G = F by abel, LinearMap.range_neg] at h
  omega

variable {X C R M : Type*} [AddCommGroup X] [Module K X]
variable [AddCommGroup M] [Module K M] [Module.Finite K M] [Fintype C] [Fintype R]
variable [DecidableEq C] [DecidableEq R]

def colInclude : (C → X) →ₗ[K] (C ⊕ R → X) where
  toFun y := Sum.elim y 0
  map_add' _ _ := by funext i; cases i <;> simp
  map_smul' _ _ := by funext i; cases i <;> simp

def rowInclude : (R → X) →ₗ[K] (C ⊕ R → X) where
  toFun x := Sum.elim 0 x
  map_add' _ _ := by funext i; cases i <;> simp
  map_smul' _ _ := by funext i; cases i <;> simp

def evaluatedGrid (f : C ⊕ R → X →ₗ[K] M) : (C ⊕ R → X) →ₗ[K] Grid (C ⊕ R) M :=
  LinearMap.pi fun p => (f p.2).comp (LinearMap.proj p.1)

theorem grid_cross_eval (f : C ⊕ R → X →ₗ[K] M)
    (B : LinearMap.BilinForm K M) (y : C → X) (x : R → X) :
    gridForm B (evaluatedGrid f (colInclude (K := K) (R := R) y))
      (evaluatedGrid f (rowInclude (K := K) (C := C) x)) =
      ∑ u : C, ∑ t : R, B (f (.inr t) (y u)) (f (.inl u) (x t)) := by
  rw [gridForm_apply, Fintype.sum_prod_type]
  simp only [Fintype.sum_sum_type, evaluatedGrid, LinearMap.pi_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Prod.swap_prod_mk]
  simp [colInclude, rowInclude]

theorem rank_ge_of_cross_kernel [Module.Finite K W] (F : LinearMap.BilinForm K V)
    (left : W →ₗ[K] V) (right : W' →ₗ[K] V)
    (h : ∀ y, (∀ x, F (left y) (right x) = 0) → y = 0) :
    finrank K W ≤ finrank K F.range := by
  let G := (right.dualMap).comp (LinearMap.comp F left)
  have hi : Function.Injective G := by
    intro y z he
    apply sub_eq_zero.mp
    apply h
    intro x
    have hzero : G (y-z) = 0 := by rw [map_sub, he, sub_self]
    exact LinearMap.congr_fun hzero x
  rw [← LinearMap.finrank_range_of_inj hi]
  exact rank_cross_le F left right

#print axioms grid_cross_eval
#print axioms rank_ge_of_cross_kernel
#print axioms correction_rank_lower

end
end Mathproof.EvenTI.Reciprocal.Four
