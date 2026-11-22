import EvenP16RecoverChartProduct
import EvenP8FourLift

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace EvenTI.P16Recover

open scoped BigOperators Matrix
open Matrix EvenTI.Action EvenTI.CellPreparation EvenTI.TrialProducer
open Mathproof.EvenOrdinaryTISingular.EnlargedCut
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPMatrixProductLoop20261001 (cost)

private theorem reindex_sandwich {K A B : Type} [Field K] [Fintype A] [Fintype B]
    {w n : ℕ} (eA : Fin w ≃ A) (eB : Fin w ≃ B)
    (L : Matrix (Fin n) B K) (G : Matrix (Fin w) (Fin w) K) (R : Matrix A (Fin n) K) :
    L * (Matrix.of fun (i : B) (j : A) => G (eB.symm i) (eA.symm j)) * R =
      (Matrix.of fun (i : Fin n) (j : Fin w) => L i (eB j)) * G *
        (Matrix.of fun (i : Fin w) (j : Fin n) => R (eA i) j) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply]
  rw [← eA.sum_comp (fun a => (∑ b : B, L i b * G (eB.symm b) (eA.symm a)) * R a j)]
  simp only [Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← eB.sum_comp (fun b => L i b * G (eB.symm b) k)]
  simp only [Equiv.symm_apply_apply]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

abbrev fourRecoveryWidth (ell rho : Coord 2 n → K) (i : Fin (2+2)) :=
  fourModeWidth ell rho (fourSiteMode i)

def targetCropNumeric (ell rho ell' rho' : Coord 2 n → K)
    (hL : rawFrameWidth ell' = rawFrameWidth ell) (hR : rawFrameWidth rho' = rawFrameWidth rho)
    (i : Fin (2+2)) : Matrix (Fin n) (Fin (fourRecoveryWidth ell rho i)) K :=
  fun j k => fourCrop ell' rho' (fourSiteOrder i) j (fourTargetOrder ell rho ell' rho' hL hR i k)

def sourcePadNumeric (ell rho : Coord 2 n → K) (i : Fin (2+2)) :
    Matrix (Fin (fourRecoveryWidth ell rho i)) (Fin n) K :=
  fun j k => fourPad ell rho (fourSiteOrder i) (fourNumericOrder ell rho i j) k

/-- Both padded-frame banks use the same numeric site order as the middle matrix. -/
theorem recoverFourMatrices_numeric (ell rho ell' rho' : Coord 2 n → K)
    (hL : rawFrameWidth ell' = rawFrameWidth ell)
    (hR : rawFrameWidth rho' = rawFrameWidth rho) (G : FourNumericUnits ell rho) (i : Fin (2+2)) :
    recoverFourMatrices ell rho ell' rho' hL hR G i =
      targetCropNumeric ell rho ell' rho' hL hR i * (G i).val * sourcePadNumeric ell rho i := by
  change fourCrop ell' rho' (fourSiteOrder i) *
    relabelRectangular fourSiteOrder (fourNumericOrder ell rho)
      (fourTargetOrder ell rho ell' rho' hL hR) G (fourSiteOrder i) *
        fourPad ell rho (fourSiteOrder i) = _
  unfold relabelRectangular
  rw [Equiv.piCongr_apply_apply]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact reindex_sandwich (fourNumericOrder ell rho i) (fourTargetOrder ell rho ell' rho' hL hR i)
    (fourCrop ell' rho' (fourSiteOrder i)) (G i).val (fourPad ell rho (fourSiteOrder i))

#print axioms recoverFourMatrices_numeric

/-- Execute the order-four crop from the physical frames and decharted matrix. -/
theorem recoverFourSite_run (F : FieldPresentation K) (ell rho ell' rho' : Coord 2 n → K)
    (hL : rawFrameWidth ell' = rawFrameWidth ell) (hR : rawFrameWidth rho' = rawFrameWidth rho)
    (G : FourNumericUnits ell rho) (i : Fin (2+2)) {B S : ℕ} {s : Env}
    (hIn : TriProductInput F B S n (fourRecoveryWidth ell rho i) (fourRecoveryWidth ell rho i) n s)
    (hCrop : matrix F s (s.vars triLeft) n (fourRecoveryWidth ell rho i) =
      targetCropNumeric ell rho ell' rho' hL hR i)
    (hMiddle : matrix F s (s.vars canonical.aBase) (fourRecoveryWidth ell rho i)
      (fourRecoveryWidth ell rho i) = (G i).val)
    (hPad : matrix F s (s.vars canonical.bBase) (fourRecoveryWidth ell rho i) n = sourcePadNumeric ell rho i) :
    ∃ t, Run B triProduct s t (cost F.e (fourRecoveryWidth ell rho i) (fourRecoveryWidth ell rho i) n +
        13 + cost F.e n (fourRecoveryWidth ell rho i) n) ∧
      ValidMemory F B t ∧ Slots F canonical "even.scalar.ws" S B t ∧
      matrix F t (s.vars triOut) n n = recoverFourMatrices ell rho ell' rho' hL hR G i ∧
      t.inp = s.inp ∧ t.out = s.out := by
  obtain ⟨t,hr,hMem,hSlots,hOut,hInp,hTape⟩ := triProduct_run F hIn
  refine ⟨t,hr,hMem,hSlots,?_,hInp,hTape⟩
  rw [hOut,hCrop,hMiddle,hPad,recoverFourMatrices_numeric,Matrix.mul_assoc]

#print axioms recoverFourSite_run
end EvenTI.P16Recover
