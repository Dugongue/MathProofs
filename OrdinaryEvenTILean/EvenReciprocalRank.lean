import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank bounds for the large-label rectangular shear calculation. -/
namespace Mathproof.EvenTI.Reciprocal
open scoped Matrix
open Matrix Module LinearMap

section General
variable {K U V W : Type*} [Field K]
variable [AddCommGroup U] [Module K U] [FiniteDimensional K U]
variable [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem postcompose_rank_loss (f : U →ₗ[K] V) (g : V →ₗ[K] W) :
    finrank K f.range ≤ finrank K (g.comp f).range + finrank K g.ker := by
  let g' := g.comp f.range.subtype
  have hR : g'.range = (g.comp f).range := by
    rw [LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]
  let i : g'.ker →ₗ[K] g.ker :=
    (f.range.subtype.comp g'.ker.subtype).codRestrict _ (fun x => x.property)
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : g.ker => z.val) h
  have hK := LinearMap.finrank_le_finrank_of_injective hi
  have h := g'.finrank_range_add_finrank_ker
  rw [hR] at h
  omega

theorem precompose_rank_loss (f : U →ₗ[K] V) (g : V →ₗ[K] W) :
    finrank K g.range ≤ finrank K (g.comp f).range + (finrank K V - finrank K f.range) := by
  obtain ⟨T, hT⟩ := Submodule.exists_isCompl f.range
  have hh : g.range = f.range.map g ⊔ T.map g := by
    rw [← Submodule.map_sup, hT.sup_eq_top, Submodule.map_top]
  rw [hh, LinearMap.range_comp]
  have hd := Submodule.finrank_add_eq_of_isCompl hT
  calc
    _ ≤ finrank K (f.range.map g) + finrank K (T.map g) := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq (f.range.map g) (T.map g)
      omega
    _ ≤ _ := by
      have hm : finrank K (T.map g) ≤ finrank K T := Submodule.finrank_map_le _ _
      omega

end General

section Matrices
variable {K A I B J : Type*} [Field K] [Fintype A] [Fintype I] [Fintype B] [Fintype J]

private noncomputable def rowRangeEquiv (V : Matrix B J K) :
    (mulRightLinearMap I K V).range ≃ₗ[K] (I → V.vecMulLinear.range) := by
  classical
  let f : (mulRightLinearMap I K V).range →ₗ[K] (I → V.vecMulLinear.range) :=
    { toFun := fun Y i => ⟨Y.val i, by
        obtain ⟨U, hU⟩ := Y.property
        exact ⟨U i, congrFun hU i⟩⟩
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro Y Z h
    apply Subtype.ext
    funext i
    exact congrArg (fun x : I → V.vecMulLinear.range => (x i).val) h
  · intro rows
    choose U hU using fun i => (rows i).property
    refine ⟨⟨fun i => (rows i).val, ⟨U, funext hU⟩⟩, ?_⟩
    funext i
    rfl

theorem mulRight_finrank_range (V : Matrix B J K) :
    finrank K (mulRightLinearMap I K V).range = Fintype.card I * V.rank := by
  rw [(rowRangeEquiv (I := I) V).finrank_eq, Module.finrank_pi_fintype,
    V.rank_eq_finrank_span_row, range_vecMulLinear]
  simp [nsmul_eq_mul]

theorem right_multiplication_deficit (V : Matrix B I K) :
    finrank K (Matrix I I K) - finrank K (mulRightLinearMap I K V).range =
      Fintype.card I * (Fintype.card I - V.rank) := by
  rw [mulRight_finrank_range, finrank_matrix, Module.finrank_self, mul_one,
    Nat.mul_sub_left_distrib]

private noncomputable def colRangeEquiv (V : Matrix A I K) :
    (mulLeftLinearMap J K V).range ≃ₗ[K] (J → V.mulVecLin.range) := by
  classical
  let f : (mulLeftLinearMap J K V).range →ₗ[K] (J → V.mulVecLin.range) :=
    { toFun := fun Y j => ⟨fun i => Y.val i j, by
        obtain ⟨U, hU⟩ := Y.property
        refine ⟨fun i => U i j, ?_⟩
        funext i
        exact congrFun (congrFun hU i) j⟩
      map_add' := fun _ _ => by ext; rfl
      map_smul' := fun _ _ => by ext; rfl }
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · intro Y Z h
    apply Subtype.ext
    funext i j
    exact congrArg (fun x : J → V.mulVecLin.range => (x j).val i) h
  · intro cols
    choose U hU using fun j => (cols j).property
    refine ⟨⟨fun i j => (cols j).val i, ?_⟩, ?_⟩
    · refine ⟨fun i j => U j i, ?_⟩
      funext i j
      exact congrFun (hU j) i
    · funext j
      rfl

theorem mulLeft_finrank_range (V : Matrix A I K) :
    finrank K (mulLeftLinearMap J K V).range = Fintype.card J * V.rank := by
  rw [(colRangeEquiv (J := J) V).finrank_eq, Module.finrank_pi_fintype]
  simp [nsmul_eq_mul, Matrix.rank]

theorem left_multiplication_kernel (V : Matrix B I K) :
    finrank K (mulLeftLinearMap I K V).ker =
      Fintype.card I * (Fintype.card I - V.rank) := by
  have h := (mulLeftLinearMap I K V).finrank_range_add_finrank_ker
  rw [mulLeft_finrank_range, finrank_matrix, Module.finrank_self, mul_one] at h
  rw [Nat.mul_sub_left_distrib]
  omega

/-- Right and left multiplication together lose at most one row-dimension
for each missing unit of their respective ranks. -/
theorem rectangular_sandwich_rank (V M : Matrix B I K)
    (L : Matrix I I K →ₗ[K] Matrix I I K) :
    finrank K L.range ≤
      finrank K ((mulLeftLinearMap I K M).comp
        (L.comp (mulRightLinearMap I K V))).range +
      Fintype.card I * (Fintype.card I - V.rank) +
      Fintype.card I * (Fintype.card I - M.rank) := by
  have h₁ := precompose_rank_loss (mulRightLinearMap I K V) L
  have h₂ := postcompose_rank_loss (L.comp (mulRightLinearMap I K V))
    (mulLeftLinearMap I K M)
  rw [right_multiplication_deficit] at h₁
  rw [left_multiplication_kernel] at h₂
  omega

end Matrices
end Mathproof.EvenTI.Reciprocal

#print axioms Mathproof.EvenTI.Reciprocal.rectangular_sandwich_rank
