import PolarAssemblyRank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Mathproof.EvenTI.Reciprocal.Next

open scoped BigOperators
open Module LinearMap
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

variable {K J W V : Type*} [Field K] [Fintype J] [DecidableEq J]
variable [AddCommGroup W] [Module K W] [Module.Finite K W]
variable [AddCommGroup V] [Module K V] [Module.Finite K V]

abbrev Grid (J W : Type*) := J × J → W

/-- The natural pairing indexed by a transpose of the block positions. -/
def flipDual : Grid J (Module.Dual K W) →ₗ[K] Module.Dual K (Grid J W) where
  toFun a :=
    { toFun := fun y => ∑ p : J × J, a p (y p.swap)
      map_add' y z := by simp [Finset.sum_add_distrib]
      map_smul' k y := by simp [Finset.mul_sum] }
  map_add' a b := by ext y; simp [Finset.sum_add_distrib]
  map_smul' k a := by ext y; simp [Finset.mul_sum]

theorem flipDual_single (a : Grid J (Module.Dual K W)) (q : J × J) (x : W) :
    flipDual a (Pi.single q.swap x) = a q x := by
  change (∑ p : J × J, a p ((Pi.single q.swap x : Grid J W) p.swap)) = a q x
  rw [Finset.sum_eq_single q]
  · simp
  · intro p _ hp
    have hne : p.swap ≠ q.swap := by
      intro he
      apply hp
      simpa using congrArg Prod.swap he
    simp [Pi.single_eq_of_ne hne]
  · simp

theorem flipDual_injective :
    Function.Injective (flipDual (K := K) (J := J) (W := W)) := by
  intro a b h
  funext q
  apply LinearMap.ext
  intro x
  simpa only [flipDual_single] using
    congrArg (fun f : Module.Dual K (Grid J W) => f (Pi.single q.swap x)) h

def gridForm (B : LinearMap.BilinForm K W) : LinearMap.BilinForm K (Grid J W) :=
  flipDual.comp (LinearMap.compLeft B (J × J))

theorem gridForm_apply (B : LinearMap.BilinForm K W) (a b : Grid J W) :
    gridForm B a b = ∑ p : J × J, B (a p) (b p.swap) := rfl

private noncomputable def rangeCompLeftEquiv (B : LinearMap.BilinForm K W) :
    (LinearMap.compLeft B (J × J)).range ≃ₗ[K] Grid J B.range := by
  classical
  have h := LinearMap.range_compLeft B (J × J)
  refine
    { toFun := fun x p => ⟨x.val p, by
        obtain ⟨x, hx⟩ := x
        rw [h] at hx
        exact hx p (Set.mem_univ p)⟩
      invFun := fun x => ⟨fun p => (x p).val, by
        rw [h]
        exact fun p _ => (x p).property⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

set_option backward.isDefEq.respectTransparency false in
theorem gridForm_rank (B : LinearMap.BilinForm K W) :
    finrank K (gridForm (J := J) B).range = Fintype.card J ^ 2 * finrank K B.range := by
  classical
  let b := Basis.ofVectorSpace K (↥B.range)
  letI : Fintype (Basis.ofVectorSpaceIndex K (↥B.range)) := inferInstance
  let E : Grid J B.range ≃ₗ[K] Matrix (J × J) (Basis.ofVectorSpaceIndex K (↥B.range)) K :=
    LinearEquiv.piCongrRight (fun _ => b.equivFun)
  have hd : finrank K (Grid J B.range) = Fintype.card J ^ 2 * finrank K B.range := by
    rw [E.finrank_eq, Module.finrank_matrix, b.equivFun.finrank_eq, Module.finrank_pi]
    simp [pow_two]
  unfold gridForm
  rw [LinearMap.range_comp, ← (Submodule.equivMapOfInjective _ flipDual_injective _).finrank_eq,
    (rangeCompLeftEquiv (J := J) B).finrank_eq, hd]

def diagFold : Grid J W →ₗ[K] W where
  toFun x := ∑ j : J, x (j,j)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' k x := by simp [Finset.smul_sum]

/-- Rank subadditivity records exactly how much can be lost by including the
single forced diagonal sum block. -/
private theorem finrank_range_add_le {A C : Type*} [AddCommGroup A] [Module K A]
    [Module.Finite K A] [AddCommGroup C] [Module K C] (f g : A →ₗ[K] C) :
    finrank K (f + g).range ≤ finrank K f.range + finrank K g.range := by
  have hle : (f + g).range ≤ f.range ⊔ g.range := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.mpr ⟨f x, ⟨x,rfl⟩, g x, ⟨x,rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem rank_of_grid_and_sum (B : LinearMap.BilinForm K W) :
    (Fintype.card J ^ 2 - 1) * finrank K B.range ≤
      finrank K (gridForm (J := J) B + B.compl₁₂ (diagFold (J := J)) (diagFold (J := J))).range := by
  let f := gridForm (J := J) B
  let g := B.compl₁₂ (diagFold (J := J)) (diagFold (J := J))
  have hg : finrank K g.range ≤ finrank K B.range := rank_pullback_le B _
  have h := finrank_range_add_le (f + g) (-g)
  have hcancel : f + g + -g = f := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change (f x y + g x y) + -(g x y) = f x y
    abel
  have hneg : (-g).range = g.range := LinearMap.range_neg _
  rw [hcancel, hneg] at h
  have hr : finrank K f.range = Fintype.card J ^ 2 * finrank K B.range := gridForm_rank B
  rw [hr] at h
  change (Fintype.card J ^ 2 - 1) * finrank K B.range ≤ finrank K (f + g).range
  rw [Nat.sub_mul, one_mul]
  omega

/-- A surjective family of independently controlled rows pulls back the
polar rank without loss. -/
theorem rank_of_surjective_grid (B : LinearMap.BilinForm K W) (D : V →ₗ[K] Grid J W)
    (hD : Function.Surjective D) :
    (Fintype.card J ^ 2 - 1) * finrank K B.range ≤
      finrank K ((gridForm (J := J) B + B.compl₁₂ (diagFold (J := J)) (diagFold (J := J))).compl₁₂ D D).range := by
  let F := gridForm (J := J) B + B.compl₁₂ (diagFold (J := J)) (diagFold (J := J))
  obtain ⟨R, hR⟩ := D.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hD)
  have hi : (F.compl₁₂ D D).compl₁₂ R R = F := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    change F (D (R v)) (D (R w)) = F v w
    have hv : D (R v) = v := LinearMap.congr_fun hR v
    have hw : D (R w) = w := LinearMap.congr_fun hR w
    rw [hv, hw]
  have h := rank_pullback_le (F.compl₁₂ D D) R
  rw [hi] at h
  exact (rank_of_grid_and_sum B).trans h

#print axioms gridForm_rank
#print axioms rank_of_grid_and_sum
#print axioms rank_of_surjective_grid

end Mathproof.EvenTI.Reciprocal.Next



