import EvenP16AnchorCrossMeaning
import EvenP16AnchorSquareTrace

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace EvenTI.P16Execution

open EvenTI.Action EvenTI.Contract EvenTI.P15Execution
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Coverage
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.P15RecogIMPDot20261007 (qN dI dL dT dU dZ dO)
open Mathproof.P15RecogIMPGrid20261007 (Written gRows gCols gOut gU gV)
open scoped BigOperators Matrix

variable {K : Type} [Field K] [Fintype K]

noncomputable def reciprocalAnchorGrid (F : FieldPresentation K) (mirror : Bool) : Com :=
  .seq (crossGrid F mirror) (squareTrace F)

/-- The complete reciprocal anchor computation after its cut and reciprocal
have been installed. Both mirror choices and every retained mode share the
same rectangular-grid and partial-trace checks. -/
theorem reciprocalAnchorGrid_run (F : FieldPresentation K) {l n B S src inv cross square o tt uu z one : ℕ}
    {s : Env} (T : Tensor K ((l+1)+(l+1)) n) (N : Matrix (Coord (l+1) n) (Coord (l+1) n) K)
    (mode : HigherModes l) (hn : 0 < n)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1 < B) (hNN : n*n+1 < B)
    (hA : (n^l)*(n^l)+1 < B)
    (hSrcSep : src+(n*n^l)*(n*n^l) ≤ cross) (hInvSep : inv+(n*n^l)*(n*n^l) ≤ cross)
    (hCross : cross+(n*n)*(n*n) ≤ square) (hSquare : square+(n*n)*(n*n) ≤ S) (hOut : o+n*n ≤ square)
    (hT : tt < src ∧ tt < inv ∧ tt < o) (hU : uu < src ∧ uu < inv ∧ uu < o) (hTU : tt≠uu)
    (hZ : z < o ∧ z < cross ∧ z≠tt ∧ z≠uu) (hOne : one < o ∧ one < cross ∧ one≠tt ∧ one≠uu)
    (hR : s.vars gRows=n*n) (hC : s.vars gCols=n*n) (hL : s.vars dL=(n^l)*(n^l))
    (hO : s.vars gOut=cross) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu) (hZR : s.vars dZ=z)
    (hNr : s.vars crossN=n) (hAr : s.vars crossA=n^l) (hStride : s.vars crossStride=n^(l-mode.2.val))
    (hSrc : s.vars crossSource=src) (hInv : s.vars crossInverse=inv)
    (hSide : s.vars anchorSideWord=n) (hCrossW : s.vars anchorCrossWord=cross)
    (hSquareW : s.vars anchorSquareWord=square) (hTraceW : s.vars anchorTraceWord=o)
    (hOneW : s.vars anchorUnitWord=one)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hLoad : InstalledCutMatrix F s l n src (flatten T)) (hRecip : InstalledCutMatrix F s l n inv N) :
    ∃ t, Run B (reciprocalAnchorGrid F mode.1) s t
      (crossGridCost F mode.1 n (n^l)+squareTraceCost F n) ∧ Slots F canonical qN.WS S B t ∧
      (∀ i j : Fin n, val F canonical qN.WS t (o+(i.val*n+j.val)) = rawReciprocalAnchor T N mode i j) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  have hZkeep : ¬ Written cross (n*n) (n*n) tt uu z := by unfold Written; omega
  have hOneKeep : ¬ Written cross (n*n) (n*n) tt uu one := by unfold Written; omega
  obtain ⟨u,hr,hs,hVals,hKeep,hRegs,hi,ho⟩ := crossGrid_run F mode.1 mode.2 hn hS hNN hA
    (by omega) (by omega) hSrcSep hInvSep (hCross.trans (by omega)) (by omega) (by omega) (by omega) hTU
    ⟨hT.1,hT.2.1⟩ ⟨hU.1,hU.2.1⟩ hZkeep hZero hR hC hL hO hTR hUR hZR hNr hAr hStride hSrc hInv
  let X : Matrix (Fin n × Fin n) (Fin n × Fin n) K := reciprocalFront (flatten T) mode * reciprocalBack N mode
  have hX (i j : Fin n × Fin n) : val F canonical qN.WS u
      (cross+(pairWordIndex i*(n*n)+pairWordIndex j)) = X i j := by
    have eq (p : Fin n × Fin n) : pairWordIndex p = (finProdFinEquiv p).val := by
      simp [pairWordIndex,finProdFinEquiv,Nat.mul_comm,Nat.add_comm]
    rw [eq i,eq j,hVals _ (finProdFinEquiv i).isLt _ (finProdFinEquiv j).isLt]
    simpa only [Equiv.symm_apply_apply,X] using
      crossedSum_eq_panels F hn mode (finProdFinEquiv i) (finProdFinEquiv j) (flatten T) N hLoad hRecip
  obtain ⟨t,rt,hSt,hEnd,_,_,hIt,hOt⟩ := squareTrace_run F X hs hN hNN hCross hSquare hOut
    ⟨by omega,hT.2.2⟩ ⟨by omega,hU.2.2⟩ hTU hZ hOne
    ((hRegs dZ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hZR)
    ((hRegs dT (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTR)
    ((hRegs dU (by decide) (by decide) (by decide) (by decide) (by decide)).trans hUR)
    ((hRegs gRows (by decide) (by decide) (by decide) (by decide) (by decide)).trans hR)
    ((hRegs gCols (by decide) (by decide) (by decide) (by decide) (by decide)).trans hC)
    ((hRegs anchorSideWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSide)
    ((hRegs anchorCrossWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hCrossW)
    ((hRegs anchorSquareWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hSquareW)
    ((hRegs anchorTraceWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hTraceW)
    ((hRegs anchorUnitWord (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOneW)
    ((hKeep z (by omega) hZkeep).trans hZero) ((hKeep one (by omega) hOneKeep).trans hUnit) hX
  refine ⟨t,hr.seq rt,hSt,?_,hIt.trans hi,hOt.trans ho⟩
  intro i j
  rw [rawReciprocalAnchor_eq_products]
  exact hEnd i j

#print axioms reciprocalAnchorGrid_run
end EvenTI.P16Execution