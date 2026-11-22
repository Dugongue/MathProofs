import EvenP19TrialHigherContraction
import EvenP19TrialSideTrace

set_option autoImplicit false
set_option maxHeartbeats 950000
set_option maxRecDepth 22000

namespace EvenTI.P19Trial

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.AnchorCovariance
open EvenTI.P10Scan EvenTI.P15Trial EvenTI.P16Trial EvenTI.P16Execution EvenTI.PrimaryAlignment
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dT dU dZ)
open Mathproof.P15RecogIMPGrid20261007 (gRows gCols)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private noncomputable def testField : FieldPresentation (ZMod 2) :=
  Classical.choice (Mathproof.Problem18FieldPresentation20260930.exists_fieldPresentation (ZMod 2))

private theorem contractionTraceSafe (F : FieldPresentation K) :
    ∀ r ∈ [dT,dU,dZ,anchorSideWord,anchorCrossWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
      fieldVectorStart,fieldVectorLength,emitAnchorWidth], r ∉ scalarWrites (higherContraction F) := by
  change ∀ r ∈ [dT,dU,dZ,anchorSideWord,anchorCrossWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
    fieldVectorStart,fieldVectorLength,emitAnchorWidth], r ∉ scalarWrites (higherContraction testField)
  decide

noncomputable def higherAnchorTail (D : FieldEncoding K) (F : FieldPresentation K) (side : Bool) : Com :=
  .seq (higherContraction F) (sideTraceRecord D F side)

noncomputable def higherAnchorTailCost (F : FieldPresentation K) (side : Bool) (m n : ℕ) : ℕ :=
  higherContractionCost F m n + sideTraceRecordCost F side n

structure TraceRegisterBank (s : Env) (n square o one : ℕ) : Prop where
  side : s.vars anchorSideWord=n
  square : s.vars anchorSquareWord=square
  traced : s.vars anchorTraceWord=o
  one : s.vars anchorUnitWord=one
  emitStart : s.vars fieldVectorStart=o
  emitLen : s.vars fieldVectorLength=n*n
  emitWidth : s.vars emitAnchorWidth=n

/-- Use the actual native projection matrices to emit a higher singular
an anchor for one retained mode and side, with the reference field-word encoding. -/
theorem higherAnchorTail_run (D : FieldEncoding K) (F : FieldPresentation K) (side : Bool)
    {B S l n : ℕ} {s : Env} (b : ContractionOffsets) (square o : ℕ)
    (T : Tensor K ((l+1)+(l+1)) n) (ell rho : Coord (l+1) n → K) (i : Fin (l+1))
    (hS : Slots F canonical qN.WS S B s) (hn : 0<n) (hnB : n+1<B)
    (hmB : n^(l+1)+1<B) (hnnB : n*n+1<B) (hR : ContractionRegisters s (n^(l+1)) n b)
    (hTrace : TraceRegisterBank s n square o b.one) (hQ : Fintype.card K ≤ B) (hP : F.p < B)
    (hT : b.tensor+n^(l+1)*n^(l+1) ≤ b.tmp)
    (hL : b.left+(n*n)*n^(l+1) ≤ b.tmp) (hQb : b.right+(n*n)*n^(l+1) ≤ b.tmp)
    (hTmp : b.tmp+n^(l+1)*(n*n) ≤ b.product) (hProd : b.product+(n*n)*(n*n) ≤ b.cross)
    (hCross : b.cross+(n*n)*(n*n) ≤ square) (hSq : square+(n*n)*(n*n) ≤ S)
    (hOut : o+n*n ≤ square) (hOutBefore : o ≤ b.tmp)
    (ht : b.tt<b.tensor ∧ b.tt<b.right ∧ b.tt<b.left ∧ b.tt<o)
    (hu : b.uu<b.tensor ∧ b.uu<b.right ∧ b.uu<b.left ∧ b.uu<o) (htu : b.tt≠b.uu)
    (hz : b.zero<o ∧ b.zero≠b.tt ∧ b.zero≠b.uu)
    (hOne : b.one<o ∧ b.one≠b.tt ∧ b.one≠b.uu)
    (hzv : val F canonical qN.WS s b.zero=0) (hov : val F canonical qN.WS s b.one=1)
    (hReadA : ∀ x y : Fin (n^(l+1)), val F canonical qN.WS s (b.tensor+(x.val*n^(l+1)+y.val))=
      flatten T ((inputCoordOrder n (l+1)).symm x) ((inputCoordOrder n (l+1)).symm y))
    (hReadL : ∀ (u : Fin (n*n)) (x : Fin (n^(l+1))),
      val F canonical qN.WS s (b.left+(u.val*n^(l+1)+x.val))=projectionCoefficients (rawRetainedProjection i ell)
        (finProdFinEquiv.symm u) ((inputCoordOrder n (l+1)).symm x))
    (hReadR : ∀ (u : Fin (n*n)) (y : Fin (n^(l+1))),
      val F canonical qN.WS s (b.right+(u.val*n^(l+1)+y.val))=projectionCoefficients (rawRetainedProjection i rho)
        (finProdFinEquiv.symm u) ((inputCoordOrder n (l+1)).symm y)) :
    ∃ t, Run B (higherAnchorTail D F side) s t (higherAnchorTailCost F side (n^(l+1)) n) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ k < o, k≠b.tt → k≠b.uu → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r ∉ scalarWrites (higherContraction F) → SideTraceStable F r → t.vars r=s.vars r) ∧
      t.inp=s.inp ∧
      t.out=s.out++blockW (numberedAnchorWords D (numeric (rawHigherSingularAnchors ell rho T (i,side)))) := by
  let A := flatten T
  let P := rawRetainedProjection i ell
  let Q := rawRetainedProjection i rho
  obtain ⟨u,r,hU,hRows,hCols,hMat,hMem,hInp,hOut₀⟩ :=
    higherContraction_run F b A P Q (inputCoordOrder n (l+1)).symm hS hn hmB hnnB hR hT hL hQb hTmp hProd
      (by omega) ⟨ht.1,ht.2.1,ht.2.2.1⟩ ⟨hu.1,hu.2.1,hu.2.2.1⟩ htu
      ⟨by omega,hz.2⟩ ⟨by omega,hOne.2⟩ hzv hov hReadA hReadL hReadR
  have keep {name : String} {value : ℕ} (hv : s.vars name=value)
      (hnm : name ∈ [dT,dU,dZ,anchorSideWord,anchorCrossWord,anchorSquareWord,anchorTraceWord,anchorUnitWord,
        fieldVectorStart,fieldVectorLength,emitAnchorWidth]) : u.vars name=value :=
    ((Frame.of_run r).vars name (contractionTraceSafe F name hnm)).trans hv
  obtain ⟨τ,h₂,hτ,hM,hRegs,hI,hOut₂⟩ := sideTraceRecord_run D F side (coordinateProjection P Q A) hU hnB hnnB
    hCross hSq hOut ⟨by omega,ht.2.2.2⟩ ⟨by omega,hu.2.2.2⟩ htu
    ⟨hz.1,by omega,hz.2⟩ ⟨hOne.1,by omega,hOne.2⟩
    (keep hR.zero (by decide)) (keep hR.tt (by decide)) (keep hR.uu (by decide))
    hRows hCols (keep hTrace.side (by decide)) (keep hR.target (by decide))
    (keep hTrace.square (by decide)) (keep hTrace.traced (by decide)) (keep hTrace.one (by decide))
    ((hMem _ (by omega) hz.2.1 hz.2.2).trans hzv)
    ((hMem _ (by omega) hOne.2.1 hOne.2.2).trans hov) hMat hQ hP
    (keep hTrace.emitStart (by decide)) (keep hTrace.emitLen (by decide)) (keep hTrace.emitWidth (by decide))
  refine ⟨τ,r.seq h₂,hτ,fun k hk ht hu => (hM k hk ht hu).trans (hMem k (by omega) ht hu),
    fun v hv ht => (hRegs v ht).trans ((Frame.of_run r).vars v hv),hI.trans hInp,?_⟩
  rw [hOut₂,hOut₀] <;> cases side <;> rfl

#print axioms higherAnchorTail_run
end EvenTI.P19Trial
