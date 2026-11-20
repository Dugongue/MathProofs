import EvenP1LawSelectedPhysical
import EvenP3RecipLowSparse
import EvenP3RecipLowQuotient

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.Sampling Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenOrdinaryTISingular (uniformFraction)

noncomputable section

variable {K H L J R I B BL : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype R] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq R]
variable [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option (J ⊕ R)) (I := I) (B := B)
local notation "Rows" => (Sum H L × Option (J ⊕ R))
local notation "Cols" => (I × B)
local notation "Primal" => (Matrix I B K)
local notation "T" => (traceKernel (K := K) (I := I))

private def reshape : (Cols → K) ≃ₗ[K] Primal where
  toFun f := fun i b => f (i,b)
  invFun X := fun p => X p.1 p.2
  left_inv f := by funext p; rcases p with ⟨i,b⟩; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def primalLabels (low : BL ↪ L) : BL ↪ Rows where
  toFun b := (.inr (low b), none)
  inj' _ _ h := low.injective (Sum.inr.inj (congrArg Prod.fst h))

private def dualLabels {a : ℕ} (high : Fin a ↪ H) : (Fin a × J) ↪ Rows where
  toFun p := (.inl (high p.1), some (.inl p.2))
  inj' p q h := Prod.ext
    (high.injective (Sum.inl.inj (congrArg Prod.fst h)))
    (Sum.inl.inj (Option.some.inj (congrArg Prod.snd h)))

private theorem labels_disjoint {a : ℕ} (high : Fin a ↪ H) (low : BL ↪ L)
    (i : BL) (j : Fin a × J) :
    primalLabels (H := H) (J := J) (R := R) low i ≠ dualLabels (L := L) (R := R) high j := by
  intro h
  cases congrArg Prod.fst h

def actualSmallRows {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L) :
    RowSample K BL (Fin a × J) Primal :=
  selectPairRows reshape (primalLabels low) (dualLabels high) (labels_disjoint high low) A

theorem actualSmallRows_primal {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L) (b : BL) :
    (actualSmallRows A high low).1.val b = Coverage.selectedPrimal A low b := by
  ext i j
  change basisOfPair A (Sum.inr (low b), none) (i, j) = A.val.1 (Sum.inr (low b), none) (i, j)
  exact basisOfPair_apply A _ _

theorem actualSmallRows_dual {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L)
    (i : Fin a) (t : J) :
    ((actualSmallRows A high low).2.val (i,t)).val =
      rectDual (Coverage.selectedDual A high i (.inl t)) := by
  apply LinearMap.ext
  intro X
  change ((basisOfPair A).map reshape).dualBasis (Sum.inl (high i), some (Sum.inl t)) X = _
  have h :
      ((basisOfPair A).map reshape).dualBasis (Sum.inl (high i), some (Sum.inl t)) X =
        (basisOfPair A).dualBasis (Sum.inl (high i), some (Sum.inl t)) (reshape.symm X) := by
    simp only [Basis.dualBasis_apply, Basis.map_repr, LinearEquiv.trans_apply]
  rw [h, basisOfPair_dual_apply, rectDual_apply]
  simp [dotProduct, Coverage.selectedDual, matrixDual, reshape, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]

private theorem sum_zeroExtend_smul {X Y W : Type*} [Fintype X] [Fintype Y]
    [AddCommMonoid W] [Module K W] (e : X ↪ Y) (x : X → K) (g : Y → W) :
    (∑ y, Coverage.zeroExtend e x y • g y) = ∑ u, x u • g (e u) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    simp only [Coverage.zeroExtend, e.injective.extend_apply]
  · intro c _ hc
    have he : ¬ ∃ a, e a = c := by
      rintro ⟨a, rfl⟩
      exact hc (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
    rw [Coverage.zeroExtend, Function.extend_apply' _ _ _ he]
    simp

private theorem sum_zeroExtend_sum {X Y Z W : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [AddCommMonoid W] [Module K W] (e : X ↪ Y) (z : X → Z → K) (g : Y → Z → W) :
    (∑ y, ∑ b, Coverage.zeroExtend e (fun a => z a b) y • g y b) =
      ∑ a, ∑ b, z a b • g (e a) b := by
  rw [Finset.sum_comm]
  simp_rw [sum_zeroExtend_smul]
  rw [Finset.sum_comm]

def sampledQuotientRows {a : ℕ} {W : Type*} [AddCommGroup W] [Module K W]
    (g : T →ₗ[K] W) (s : RowSample K BL (Fin a × J) Primal) :
    (Fin a → BL → K) →ₗ[K] (J → W) :=
  quotientRows g s.1.val (fun i t => s.2.val (i,t))

/-- The actual projected rows contain the sample as a literal coefficient
rectangle. Each coefficient outside the selected rows and columns is zero. -/
theorem smallRows_surjective_of_actualSmallRows {a : ℕ} {W : Type*}
    [AddCommGroup W] [Module K W] (g : T →ₗ[K] W)
    (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L)
    (hS : ∀ t x, rowLinear (matrixPrimal A.val.1) (matrixDual A.val.2) t x ∈ T)
    (h : Function.Surjective (sampledQuotientRows g (actualSmallRows A high low))) :
    Function.Surjective ((LinearMap.compLeft g J).comp
      (smallRows (matrixPrimal A.val.1) (matrixDual A.val.2) T hS)) := by
  intro y
  obtain ⟨x, hx⟩ := h y
  let z : H → L → K := fun a b =>
    Coverage.zeroExtend high (fun p => Coverage.zeroExtend low (x p) b) a
  refine ⟨z, ?_⟩
  funext t
  have he : smallRows (matrixPrimal A.val.1) (matrixDual A.val.2) T hS z t =
      selectedRows (actualSmallRows A high low).1.val (fun i t => (actualSmallRows A high low).2.val (i,t)) x t := by
    apply Subtype.ext
    let m (a : H) (b : L) : Matrix I I K :=
      matrixPrimal A.val.1 (.inr b, none) * matrixDual A.val.2 (.inl a, some (.inl t))
    change (∑ a, ∑ b, z a b • m a b) =
      (∑ i : Fin a, ∑ j : BL, x i j • ((actualSmallRows A high low).1.val j *
        rectDual.symm ((actualSmallRows A high low).2.val (i,t)).val))
    dsimp [z]
    rw [sum_zeroExtend_sum]
    simp_rw [sum_zeroExtend_smul, actualSmallRows_primal, actualSmallRows_dual, LinearEquiv.symm_apply_apply]
    rfl
  exact (congrArg g he).trans (congrFun hx t)

variable [Fintype K]

local instance : Fintype (PrimalRows K BL Primal) := Fintype.ofFinite _

set_option maxHeartbeats 1200000 in
theorem uniformFraction_actualSmallRows_conditioned {a : ℕ} [Nonempty Bases]
    (high : Fin a ↪ H) (low : BL ↪ L) (P : RowSample K BL (Fin a × J) Primal → Prop) :
    uniformFraction Bases (fun A => P (actualSmallRows A high low)) =
      (∑ u : PrimalRows K BL Primal,
        uniformFraction (DualRows (K := K) u.val (Fin a × J)) (fun e => P ⟨u,e⟩)) /
        Nat.card (PrimalRows K BL Primal) :=
  uniformFraction_selectPairRows (V := Primal) (R := Rows) reshape
    (primalLabels low) (dualLabels high) (labels_disjoint high low) P

#print axioms uniformFraction_actualSmallRows_conditioned
#print axioms actualSmallRows_primal
#print axioms actualSmallRows_dual

end
end Mathproof.EvenTI.Reciprocal.SquareLow
