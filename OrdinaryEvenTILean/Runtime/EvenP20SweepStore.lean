import EvenP20SweepAddress

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P20Sweep

open EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU)
open Mathproof.P15RecogIMPProgram20261007 (rOs)
open Mathproof.Problem17Primary46FactorCursor (cursor)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def storeChartRow : Com := .seq addressChart publishChart

structure RowPorts (s : Env) (n w srcX srcR Z offset i base lane : ℕ) : Prop where
  width : s.vars chartCursor=w
  ambient : s.vars savedAmbientSize=n
  basisSource : s.vars savedBasisSource=srcX
  chartSource : s.vars savedChartSource=srcR
  zero : s.vars dZ=Z
  one : s.vars rOs=Z+1
  temp1 : s.vars dT=Z+2
  temp2 : s.vars dU=Z+3
  offset : s.vars savedOffset=offset
  index : s.vars cursor=i
  bank : s.vars savedBank=base
  laneReg : s.vars savedLane=lane
  stride : s.vars savedStride=2*lane

/-- Serialize the computed chart to the row selected by the live cursor. -/
theorem storeChartRow_run (F : FieldPresentation K) {B Sn n w srcX srcR Z offset i base lane : ℕ}
    {s : Env} {A : Matrix (Fin n) (Fin n) K} {f : Polynomial K} {xs : Fin w → Fin n → K}
    (hs : Slots F canonical qN.WS Sn B s)
    (p : RowPorts s n w srcX srcR Z offset i base lane) (hw : w≤n)
    (hInd : LinearIndependent K xs)
    (hSpan : Submodule.span K (Set.range xs)=LinearMap.ker (Polynomial.aeval A f).mulVecLin)
    (hBasis : ∀ j k, val F canonical qN.WS s (srcX+(j.val*n+k.val))=xs j k)
    (hChart : ChartPrefix F s srcR w A xs)
    (hLane : n*n≤lane) (hnB : n<B) (hiB : i<B) (hRowB : offset+i<B)
    (hStride : 2*lane<B) (hCapacity : offset+i<(s.arrs savedWidths).length)
    (hSourceX : srcX+n*n≤base) (hSourceR : srcR+n*n≤base)
    (hOutput : rowChart base lane (offset+i)+lane≤Z)
    (hZ : Z+4≤Sn) (hB : Sn+10<B)
    (hz : val F canonical qN.WS s Z=0) (ho : val F canonical qN.WS s (Z+1)=1) :
    ∃ t, Run B storeChartRow s t (16+publishChartCost F w n) ∧ Slots F canonical qN.WS Sn B t ∧
      SavedChart F A f (offset+i) (rowBasis base lane (offset+i)) (rowChart base lane (offset+i)) t ∧
      (∀ k < Sn, (k < rowBasis base lane (offset+i) ∨ rowChart base lane (offset+i)+lane≤k) →
        k≠Z+2 → k≠Z+3 → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ k, k≠offset+i → (t.arrs savedWidths)[k]?=(s.arrs savedWidths)[k]?) ∧
      Frame storeChartRow s t := by
  let row := offset+i
  let X := rowBasis base lane row
  let R := rowChart base lane row
  have hx : base≤X := Nat.le_add_right _ _
  have hr : R=X+lane := rfl
  have hout : R+lane≤Z := hOutput
  obtain ⟨v,rv,hv,hrow,hX,hR,hmem,ha,frame⟩ :=
    addressChart_run F hs p.offset p.bank p.laneReg p.stride p.index hiB hRowB hStride (by
      change R<B
      omega)
  have wN : w*n≤n*n := Nat.mul_le_mul_right n hw
  have ww : w*w≤n*n := Nat.mul_le_mul hw hw
  have ports : PublishPorts v n w srcX srcR X R row Z :=
    ⟨(frame.vars _ (by decide)).trans p.width,(frame.vars _ (by decide)).trans p.ambient,
      (frame.vars _ (by decide)).trans p.basisSource,(frame.vars _ (by decide)).trans p.chartSource,
      hX,hR,hrow,(frame.vars _ (by decide)).trans p.zero,(frame.vars _ (by decide)).trans p.one,
      (frame.vars _ (by decide)).trans p.temp1,(frame.vars _ (by decide)).trans p.temp2⟩
  obtain ⟨t,rt,ht,hWidth,hBasisCopy,hChartCopy,hRest,hOther,_⟩ := publishChart_run F hv ports hw hnB
    (by omega) (by omega) (by omega) (by omega) hZ hB (by rwa [ha]) hRowB
    ((hmem _).trans hz) ((hmem _).trans ho)
  have hCompose : Run B storeChartRow s t _ := rv.seq rt
  refine ⟨t,hCompose,ht,?_,?_,?_,Frame.of_run hCompose⟩
  · exact savedChart_of_publish F hw hWidth hInd hSpan hBasis hChart
      (fun k hk => (hBasisCopy k hk).trans (hmem _))
      (fun k hk => (hChartCopy k hk).trans (hmem _))
  · intro k hk hkeep ht₁ ht₂
    change k<X ∨ R+lane≤k at hkeep
    exact (hRest k hk (by omega) (by omega) ht₁ ht₂).trans (hmem _)
  · intro k hk
    rw [hOther k hk,ha]

end EvenTI.P20Sweep

