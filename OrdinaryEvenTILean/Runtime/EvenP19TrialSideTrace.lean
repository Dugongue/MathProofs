import EvenP18TrialOppositeTrace
import EvenP17ExecutionCells
import EvenNextQuadraticCovariance
import Mathproof.Meta.Problem18FieldPresentation20260930

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 950000

namespace EvenTI.P19Trial

open EvenTI.P18Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.P15Trial EvenTI.P17Execution
open EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.AnchorCovariance
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val regNames)
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU dI dO)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols gOut gU gV Written)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private noncomputable def testField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem traceControlSafe (F : FieldPresentation K) :
    ∀ r ∈ [dT,dU,dZ,anchorSideWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
      fieldVectorStart,fieldVectorLength,emitAnchorWidth], r ∉ scalarWrites (squareTrace F) := by
  change ∀ r ∈ [dT,dU,dZ,anchorSideWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
    fieldVectorStart,fieldVectorLength,emitAnchorWidth], r ∉ scalarWrites (squareTrace testField)
  decide

private theorem emitNumericSquare_run (D : FieldEncoding K) (F : FieldPresentation K) {B S n o : ℕ}
    {s : Env} (A : Matrix (Fin n) (Fin n) K) (hS : Slots F canonical qN.WS S B s)
    (hQ : Fintype.card K≤B) (hP : F.p<B) (hN : n*n+1<B) (hFit : o+n*n≤S)
    (hO : s.vars fieldVectorStart=o) (hLen : s.vars fieldVectorLength=n*n) (hW : s.vars emitAnchorWidth=n)
    (hRead : ∀ i j : Fin n, val F canonical qN.WS s (o+(i.val*n+j.val))=A i j) :
    ∃ t, Run B (emitAnchorBlock D F) s t (emitAnchorBlockCost F n) ∧
      t.out=s.out++blockW (numberedAnchorWords D (numeric A)) ∧ t.arrs=s.arrs ∧ t.inp=s.inp ∧
      Slots F canonical qN.WS S B t ∧ (∀ x, x≠fieldVectorIndex → x≠labelAddress → t.vars x=s.vars x) := by
  apply emitAnchorBlock_framed_run D F (numeric A) hS hQ hP hN hFit hO hLen hW
  intro i
  let ij : Fin n × Fin n := finProdFinEquiv.symm i
  have hi : (finProdFinEquiv ij).val=i.val :=
    congrArg Fin.val (finProdFinEquiv.apply_symm_apply i)
  have h : (finProdFinEquiv ij).val=ij.1.val*n+ij.2.val := by simp [finProdFinEquiv,Nat.add_comm,Nat.mul_comm]
  rw [←hi,h]
  exact hRead ij.1 ij.2

noncomputable def sideTraceTail (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  if right then emitAnchorBlock D F else .seq (oppositeTraceCall F) (emitAnchorBlock D F)

noncomputable def sideTraceRecord (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  .seq (squareTrace F) (sideTraceTail D F right)

noncomputable def sideTraceRecordCost (F : FieldPresentation K) (right : Bool) (n : ℕ) : ℕ :=
  squareTraceCost F n+((if right then 0 else oppositeTraceCallCost F n)+emitAnchorBlockCost F n)

def SideTraceStable (F : FieldPresentation K) (r : String) : Prop :=
  r ∉ scalarWrites (squareTrace F) ∧ r ∉ oppositeTraceRegisters ∧ r ∉ regNames canonical ∧
    r≠dI ∧ r≠gU ∧ r≠gV ∧ r≠dO ∧ r≠fieldVectorIndex ∧ r≠labelAddress

/-- Emit a single requested side of the square's trace. The physical
caller can make two passes in the public mode order using the same banks. -/
theorem sideTraceRecord_run (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool)
    {B S n cross square o tt uu z one : ℕ} {s : Env} (A : Matrix (Fin n × Fin n) (Fin n × Fin n) K)
    (hS : Slots F canonical qN.WS S B s) (hN : n+1 < B) (hNN : n*n+1 < B)
    (hCross : cross+(n*n)*(n*n) ≤ square) (hSquare : square+(n*n)*(n*n) ≤ S)
    (hOut : o+n*n ≤ square) (hT : tt < cross ∧ tt < o) (hU : uu < cross ∧ uu < o) (hTU : tt≠uu)
    (hZ : z < o ∧ z < cross ∧ z≠tt ∧ z≠uu) (hOne : one < o ∧ one < cross ∧ one≠tt ∧ one≠uu)
    (hZR : s.vars dZ=z) (hTR : s.vars dT=tt) (hUR : s.vars dU=uu)
    (hRows : s.vars gRows=n*n) (hCols : s.vars gCols=n*n)
    (hSide : s.vars anchorSideWord=n) (hCrossW : s.vars anchorCrossWord=cross)
    (hSquareW : s.vars anchorSquareWord=square) (hTraceW : s.vars anchorTraceWord=o)
    (hOneW : s.vars anchorUnitWord=one)
    (hZero : val F canonical qN.WS s z=0) (hUnit : val F canonical qN.WS s one=1)
    (hMat : ∀ i j : Fin n × Fin n, val F canonical qN.WS s
      (cross+(pairWordIndex i*(n*n)+pairWordIndex j)) = A i j)
    (hQ : Fintype.card K≤B) (hP : F.p<B)
    (hEmO : s.vars fieldVectorStart=o) (hEmLen : s.vars fieldVectorLength=n*n) (hEmW : s.vars emitAnchorWidth=n) :
    ∃ t, Run B (sideTraceRecord D F right) s t (sideTraceRecordCost F right n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k < o, k≠tt → k≠uu → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, SideTraceStable F r → t.vars r=s.vars r) ∧ t.inp=s.inp ∧
      t.out=s.out++blockW (numberedAnchorWords D (numeric
        (if right then partialTraceRight (A^2) else partialTraceLeft (A^2)))) := by
  obtain ⟨α,r₁,hα,hTrace,hSq,hMem,hi,ho⟩ := squareTrace_run F A hS hN hNN hCross hSquare hOut
    hT hU hTU hZ hOne hZR hTR hUR hRows hCols hSide hCrossW hSquareW hTraceW hOneW hZero hUnit hMat
  have hFrame := Frame.of_run r₁
  have reg (r : String) (hr : r∈[dT,dU,dZ,anchorSideWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
      fieldVectorStart,fieldVectorLength,emitAnchorWidth]) : α.vars r=s.vars r :=
    hFrame.vars r (traceControlSafe F r hr)
  have hFit : o+n*n ≤ S := by omega
  have hLow (k : ℕ) (hk : k < o) (ht : k≠tt) (hu : k≠uu) :
      val F canonical qN.WS α k=val F canonical qN.WS s k :=
    hMem k (by omega) (by unfold Written; omega) (by unfold Written; omega)
  have hEmit {μ : Env} (J : Matrix (Fin n) (Fin n) K)
      (hμ : Slots F canonical qN.WS S B μ)
      (h₁ : μ.vars fieldVectorStart=o) (h₂ : μ.vars fieldVectorLength=n*n) (h₃ : μ.vars emitAnchorWidth=n)
      (hRead : ∀ i j : Fin n, val F canonical qN.WS μ (o+(i.val*n+j.val))=J i j) :
      ∃ t, Run B (emitAnchorBlock D F) μ t (emitAnchorBlockCost F n) ∧ Slots F canonical qN.WS S B t ∧
        (∀ k, val F canonical qN.WS t k=val F canonical qN.WS μ k) ∧
        (∀ r, r≠fieldVectorIndex → r≠labelAddress → t.vars r=μ.vars r) ∧ t.inp=μ.inp ∧
        t.out=μ.out++blockW (numberedAnchorWords D (numeric J)) := by
    obtain ⟨t,r,hOut,hArr,hI,hSlot,hReg⟩ :=
      emitNumericSquare_run D F J hμ hQ hP hNN hFit h₁ h₂ h₃ hRead
    refine ⟨t,r,hSlot,?_,hReg,hI,hOut⟩
    intro k
    unfold val slice
    rw [hArr,hReg _ (by decide) (by decide)]
  cases right with
  | true =>
    obtain ⟨t,r₂,hSlot,hKeep,hEmitReg,hIn,hEmitOut⟩ := hEmit (partialTraceRight (A^2)) hα
      ((reg _ (by decide)).trans hEmO) ((reg _ (by decide)).trans hEmLen)
      ((reg _ (by decide)).trans hEmW) hTrace
    have hRun : Run B (sideTraceRecord D F true) s t (sideTraceRecordCost F true n) := by
      simpa [sideTraceRecord,sideTraceTail,sideTraceRecordCost] using r₁.seq r₂
    refine ⟨t,hRun,hSlot,fun k hk ht hu => (hKeep k).trans (hLow k hk ht hu),
      ?_,hIn.trans hi,by simp [hEmitOut,ho]⟩
    rintro r ⟨hSq,hOpp,hC,hI,hU,hV,hO,hE,hL⟩
    exact (hEmitReg r hE hL).trans (hFrame.vars r hSq)
  | false =>
    have hSq' (i j a : Fin n) : val F canonical qN.WS α
        (traceLastGridIndex square n i.val j.val a.val)=((A^2) : Matrix (Fin n × Fin n) _ K) (i,a) (j,a) :=
      hSq (i,a) (j,a)
    obtain ⟨γ,r₂,hγ,hLeft,hWrite,hReg,hIn,hO⟩ := oppositeTraceCall_run F (A^2) hα hN hSquare
      hOut hT.2 hU.2 hTU ⟨hZ.1,hZ.2.2⟩ ⟨hOne.1,hOne.2.2⟩
      ((reg _ (by decide)).trans hTR) ((reg _ (by decide)).trans hUR)
      ((reg _ (by decide)).trans hZR) ((reg _ (by decide)).trans hSide) ((reg _ (by decide)).trans hSquareW)
      ((reg _ (by decide)).trans hTraceW) ((reg _ (by decide)).trans hOneW)
      ((hLow _ hZ.1 hZ.2.2.1 hZ.2.2.2).trans hZero)
      ((hLow _ hOne.1 hOne.2.2.1 hOne.2.2.2).trans hUnit) hSq'
    have keep {r : String} {v : ℕ} (hr : r∈[fieldVectorStart,fieldVectorLength,emitAnchorWidth])
        (h : s.vars r=v) (h₁ : r∉oppositeTraceRegisters) (h₂ : r∉regNames canonical) (h₃ : r≠dI)
        (h₄ : r≠gU) (h₅ : r≠gV) (h₆ : r≠dO) : γ.vars r=v :=
      ((hReg r h₁ h₂ h₃ h₄ h₅ h₆).trans
        (reg r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; tauto))).trans h
    obtain ⟨t,r₃,hSlot,hKeep,hEmitReg,hIn',hEmitOut⟩ := hEmit (partialTraceLeft (A^2)) hγ
      (keep (by decide) hEmO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (keep (by decide) hEmLen (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (keep (by decide) hEmW (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)) hLeft
    refine ⟨t,r₁.seq (r₂.seq r₃),hSlot,?_,?_,hIn'.trans (hIn.trans hi),by simp [hEmitOut,hO,ho]⟩
    · intro k hk ht hu
      exact (hKeep k).trans ((hWrite k (by omega) (by unfold Written; omega)).trans (hLow k hk ht hu))
    · rintro r ⟨hSq,hOpp,hC,hI,hU,hV,hO,hE,hL⟩
      exact (hEmitReg r hE hL).trans ((hReg r hOpp hC hI hU hV hO).trans (hFrame.vars r hSq))

#print axioms sideTraceRecord_run
end EvenTI.P19Trial