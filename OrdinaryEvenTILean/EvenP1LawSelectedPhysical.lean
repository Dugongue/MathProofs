import EvenP1LawMass
import EvenP1SelectedRows
import EvenP1ProbRows

namespace Mathproof.EvenTI.Reciprocal.Sampling

open Matrix Module PartOne
open scoped BigOperators Matrix

noncomputable section

variable {K H L J I B BL : Type*} [Field K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)

private def coordinateMatrix : ((I × B) → K) ≃ₗ[K] Matrix I B K where
  toFun f := fun i b => f (i, b)
  invFun X := fun p => X p.1 p.2
  left_inv f := by funext p; rcases p with ⟨i,b⟩; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private abbrev Rows := Sum H L × Option J

private def primalLabels (low : BL ↪ L) : BL ↪ Rows (H := H) (L := L) (J := J) where
  toFun i := (Sum.inr (low i), none)
  inj' a b h := low.injective (Sum.inr.inj (congrArg Prod.fst h))

private def dualLabels {a : ℕ} (high : Fin a ↪ H) :
    (Fin a × J) ↪ Rows (H := H) (L := L) (J := J) where
  toFun p := (Sum.inl (high p.1), some p.2)
  inj' p q h := Prod.ext
    (high.injective (Sum.inl.inj (congrArg Prod.fst h))) (Option.some.inj (congrArg Prod.snd h))

private theorem labels_disjoint {a : ℕ} (high : Fin a ↪ H) (low : BL ↪ L) (i : BL) (j : Fin a × J) :
    primalLabels (H := H) (J := J) low i ≠ dualLabels (L := L) high j := by
  intro h
  cases congrArg Prod.fst h

/-- The selected sample, bundled in the spaces used by the rectangular rank proof. -/
def actualRows {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L) :
    RowSample K BL (Fin a × J) (Matrix I B K) :=
  selectPairRows coordinateMatrix (primalLabels low) (dualLabels high) (labels_disjoint high low) A

theorem actualRows_primal {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L) (i : BL) :
    (actualRows A high low).1.val i = Coverage.selectedPrimal A low i := by
  ext j b
  change basisOfPair A (Sum.inr (low i), none) (j, b) = A.val.1 (Sum.inr (low i), none) (j, b)
  exact basisOfPair_apply A _ _

theorem actualRows_dual {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L) (i : Fin a) (t : J) :
    ((actualRows A high low).2.val (i,t)).val = rectDual (Coverage.selectedDual A high i t) := by
  apply LinearMap.ext
  intro X
  change ((basisOfPair A).map coordinateMatrix).dualBasis (Sum.inl (high i), some t) X = _
  have h :
      ((basisOfPair A).map coordinateMatrix).dualBasis (Sum.inl (high i), some t) X =
        (basisOfPair A).dualBasis (Sum.inl (high i), some t) (coordinateMatrix.symm X) := by
    simp only [Basis.dualBasis_apply, Basis.map_repr, LinearEquiv.trans_apply]
  rw [h, basisOfPair_dual_apply, rectDual_apply]
  simp [dotProduct, Coverage.selectedDual, matrixDual, coordinateMatrix, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type, mul_comm]

def sampledSelectedRows {a : ℕ} (s : RowSample K BL (Fin a × J) (Matrix I B K)) :
    (Fin a → BL → K) →ₗ[K] (J → Next.traceKernel (K := K) (I := I)) :=
  selectedRows s.1.val (fun i t => s.2.val (i,t))

theorem actualRows_selectedOutputs {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L)
    (x : Fin a → BL → K) (t : J) :
    (sampledSelectedRows (actualRows A high low) x t).val =
      Coverage.selectedOutputs (Coverage.selectedPrimal A low) (Coverage.selectedDual A high) x t := by
  change (∑ i : Fin a, ∑ j : BL, x i j • ((actualRows A high low).1.val j *
    rectDual.symm ((actualRows A high low).2.val (i,t)).val)) = _
  simp only [actualRows_primal, actualRows_dual, LinearEquiv.symm_apply_apply,
    Coverage.selectedOutputs]

theorem baselineRows_surjective_of_actualRows {a : ℕ} (A : Bases) (high : Fin a ↪ H) (low : BL ↪ L)
    (h : Function.Surjective (sampledSelectedRows (actualRows A high low))) :
    Function.Surjective (Next.baselineRows A) :=
  Coverage.baselineRows_surjective_of_selected A high low (fun y => by
    obtain ⟨x, hx⟩ := h y
    exact ⟨x, fun t => (actualRows_selectedOutputs A high low x t).symm.trans
      (congrArg Subtype.val (congrFun hx t))⟩)

variable [Fintype K]

set_option maxHeartbeats 1600000

/-- The exact joint law on the literal selected primal and dual rows. -/
theorem uniformFraction_actualRows {a : ℕ} [Nonempty Bases]
    (high : Fin a ↪ H) (low : BL ↪ L) (P : RowSample K BL (Fin a × J) (Matrix I B K) → Prop) :
    EvenOrdinaryTISingular.uniformFraction Bases (fun A => P (actualRows A high low)) =
      EvenOrdinaryTISingular.uniformFraction (RowSample K BL (Fin a × J) (Matrix I B K)) P :=
  uniformFraction_selectPairRows_joint (V := Matrix I B K) (R := Rows (H := H) (L := L) (J := J)) coordinateMatrix (primalLabels low) (dualLabels high)
    (labels_disjoint high low) P

local instance actualPrimalFintype : Fintype (PrimalRows K BL (Matrix I B K)) := Fintype.ofFinite _

/-- First sample an independent primal row family. For that family, sample
an independent dual row family uniformly in its annihilator. -/
theorem uniformFraction_actualRows_conditioned {a : ℕ} [Nonempty Bases]
    (high : Fin a ↪ H) (low : BL ↪ L) (P : RowSample K BL (Fin a × J) (Matrix I B K) → Prop) :
    EvenOrdinaryTISingular.uniformFraction Bases (fun A => P (actualRows A high low)) =
      (∑ u : PrimalRows K BL (Matrix I B K),
        EvenOrdinaryTISingular.uniformFraction (DualRows (K := K) u.val (Fin a × J))
          (fun e => P ⟨u, e⟩)) / Nat.card (PrimalRows K BL (Matrix I B K)) :=
  uniformFraction_selectPairRows (V := Matrix I B K) (R := Rows (H := H) (L := L) (J := J)) coordinateMatrix (primalLabels low) (dualLabels high)
    (labels_disjoint high low) P

#print axioms uniformFraction_actualRows_conditioned
#print axioms actualRows_primal
#print axioms actualRows_dual
#print axioms baselineRows_surjective_of_actualRows
#print axioms uniformFraction_actualRows

end
end Mathproof.EvenTI.Reciprocal.Sampling
