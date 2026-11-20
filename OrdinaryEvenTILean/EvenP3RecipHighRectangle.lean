import EvenP3RecipHighPhysical
import EvenP1SelectedRows

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.Problem17PolarAssembly (rank_pullback_le)

noncomputable section

variable {K A BL H L C R J I B : Type*} [Field K]
variable [Fintype A] [Fintype BL] [Fintype H] [Fintype L] [Fintype C] [Fintype R]
variable [Fintype I] [Fintype B] [Fintype J] [DecidableEq J] [DecidableEq H] [DecidableEq L] [DecidableEq C]
variable [DecidableEq R] [DecidableEq I] [DecidableEq B]

local notation "Groups" => (C ⊕ R)
local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "W" => (traceKernel (K := K) (I := I))

private def extension {X Y E : Type*} [AddCommGroup E] [Module K E] (e : X ↪ Y) :
    (X → E) →ₗ[K] (Y → E) where
  toFun f := Function.extend e f 0
  map_add' f g := by
    funext y
    by_cases h : ∃ x, e x = y
    · obtain ⟨x,rfl⟩ := h
      simp only [e.injective.extend_apply, Pi.add_apply]
    · simp [Function.extend_apply' _ _ _ h]
  map_smul' z f := by
    funext y
    by_cases h : ∃ x, e x = y
    · obtain ⟨x,rfl⟩ := h
      simp only [e.injective.extend_apply, Pi.smul_apply, RingHom.id_apply]
    · simp [Function.extend_apply' _ _ _ h]

private theorem extension_sum {X Y E : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid E] [Module K E] (e : X ↪ Y) (f : X → K) (g : Y → E) :
    (∑ y, Function.extend e f 0 y • g y) = ∑ x, f x • g (e x) := by
  change (∑ y ∈ Finset.univ, Function.extend e f 0 y • g y) = _
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    simp only [e.injective.extend_apply]
  · intro y _ hy
    have he : ¬ ∃ x, e x = y := by
      rintro ⟨x,rfl⟩
      exact hy (Finset.mem_map.mpr ⟨x,Finset.mem_univ _,rfl⟩)
    simp [Function.extend_apply' _ _ _ he]

def extendRectangle (a : A ↪ H) (b : BL ↪ L) : (A → BL → K) →ₗ[K] (H → L → K) :=
  (extension (K := K) a).comp ((extension (K := K) b).compLeft A)

def selectedReciprocalBlock (U : Bases) (t : J) : (H → L → K) →ₗ[K] W :=
  (rowLinear (matrixPrimal U.val.1) (matrixDual U.val.2) t).codRestrict W
    (baseline_row_trace_zero U t)

theorem selected_block_apply (U : Bases) (a : A ↪ H) (b : BL ↪ L)
    (t : J) (x : A → BL → K) :
    (selectedReciprocalBlock U t (extendRectangle a b x)).val =
      Coverage.selectedOutputs (Coverage.selectedPrimal U b) (Coverage.selectedDual U a) x t := by
  change (∑ i : H, ∑ j : L, Function.extend a (fun i => Function.extend b (x i) 0) 0 i j •
    (matrixPrimal U.val.1 (.inr j, none) * matrixDual U.val.2 (.inl i, some t))) = _
  rw [Finset.sum_comm]
  have he (j : L) (i : H) :
      Function.extend a (fun i => Function.extend b (x i) 0) 0 i j =
        Function.extend a (fun i => Function.extend b (x i) 0 j) 0 i := by
    by_cases h : ∃ i', a i' = i
    · obtain ⟨i',rfl⟩ := h
      simp only [a.injective.extend_apply]
    · simp [Function.extend_apply' _ _ _ h]
  simp_rw [he, extension_sum]
  rw [Finset.sum_comm]
  simp_rw [extension_sum]
  rfl

/-- The high proof can use any fixed column/row group split of the physical
nonbaseline index set. The low proof may divide the same set differently. -/
theorem reciprocal_polar_rank_of_selected_cross_groups (U : Bases)
    (e : Groups ≃ J) (a : A ↪ H) (b : BL ↪ L) (c : Module.Dual K (Matrix I I K))
    (h : ∀ y : C → A → BL → K,
      (∀ (t : R) (x : A → BL → K), (∑ u : C, labelForm W c
        (selectedReciprocalBlock U (e (.inr t)) (extendRectangle a b (y u)))
        (selectedReciprocalBlock U (e (.inl u)) (extendRectangle a b x))) = 0) → y = 0) :
    finrank K (C → A → BL → K) - finrank K (labelForm W c).range ≤
      finrank K ((squarePolar (deltaLinear (matrixPrimal U.val.1) (matrixDual U.val.2))
        (traceBlocks c)).range) := by
  let E : (Groups → A → BL → K) →ₗ[K] Restricted K H L J :=
    LinearMap.pi fun t => (extendRectangle (K := K) a b).comp (LinearMap.proj (e.symm t))
  let f (t : Groups) := (selectedReciprocalBlock U (e t)).comp (extendRectangle a b)
  let P := labelForm W c
  let primal := matrixPrimal U.val.1
  let dual := matrixDual U.val.2
  let D := gridRows primal dual W (baseline_row_trace_zero U)
  let F := (gridForm P).compl₁₂ D D
  let G := P.compl₁₂ ((diagFold (K := K) (J := J)).comp D) (diagFold.comp D)
  have hF : F.compl₁₂ E E = (gridForm P).compl₁₂ (evaluatedGrid f) (evaluatedGrid f) := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change gridForm P (D (E x)) (D (E y)) = gridForm P (evaluatedGrid f x) (evaluatedGrid f y)
    rw [gridForm_apply, gridForm_apply, ← (e.prodCongr e).sum_comp
      (fun p : J × J => P (D (E x) p) (D (E y) p.swap))]
    apply Finset.sum_congr rfl
    rintro ⟨u,t⟩ _
    have hx : D (E x) ((e.prodCongr e) (u,t)) = evaluatedGrid f x (u,t) := by
      apply Subtype.ext
      change rowLinear primal dual (e t) (extendRectangle a b (x (e.symm (e u)))) =
        rowLinear primal dual (e t) (extendRectangle a b (x u))
      rw [e.symm_apply_apply]
    have hy : D (E y) (((e.prodCongr e) (u,t)).swap) = evaluatedGrid f y (t,u) := by
      apply Subtype.ext
      change rowLinear primal dual (e u) (extendRectangle a b (y (e.symm (e t)))) =
        rowLinear primal dual (e u) (extendRectangle a b (y t))
      rw [e.symm_apply_apply]
    rw [hx,hy,Prod.swap_prod_mk]
  have hg := rank_pullback_le F E
  rw [hF] at hg
  have hraw : finrank K (C → A → BL → K) ≤ finrank K F.range :=
    (grid_rank_of_cross_groups f P h).trans hg
  have hc : finrank K G.range ≤ finrank K P.range :=
    rank_pullback_le P ((diagFold (K := K) (J := J)).comp D)
  have hsub : finrank K (C → A → BL → K) - finrank K P.range ≤
      finrank K F.range - finrank K G.range := by omega
  have hfin := hsub.trans (correction_rank_lower F G)
  change _ ≤ finrank K ((gridForm P + P.compl₁₂ diagFold diagFold).compl₁₂ D D).range at hfin
  change _ ≤ finrank K ((gridForm (labelForm W c) +
    (labelForm W c).compl₁₂ diagFold diagFold).compl₁₂ (gridRows primal dual W (baseline_row_trace_zero U))
      (gridRows primal dual W (baseline_row_trace_zero U))).range at hfin
  rw [← restricted_polar primal dual W (baseline_row_trace_zero U) c] at hfin
  exact hfin.trans (rank_pullback_le _ includeShear)

#print axioms selected_block_apply
#print axioms reciprocal_polar_rank_of_selected_cross_groups

end
end Mathproof.EvenTI.Reciprocal.Four