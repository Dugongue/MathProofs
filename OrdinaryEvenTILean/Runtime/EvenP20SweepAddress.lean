import EvenP20SweepLoop

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace EvenTI.P20Sweep

open EvenTI.P19Recover
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_mul ev_var)
open Mathproof.Problem17Primary46FactorCursor (cursor)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def savedOffset : String := "even.recover.save.offset"
def savedBank : String := "even.recover.save.bank"
def savedLane : String := "even.recover.save.lane"
def savedStride : String := "even.recover.save.stride"
def savedDelta : String := "even.recover.save.delta"

def rowBasis (base lane row : ℕ) : ℕ := base+row*(2*lane)
def rowChart (base lane row : ℕ) : ℕ := rowBasis base lane row+lane

def addressChart : Com :=
  .seq (.assign savedRow (.add (.var savedOffset) (.var cursor)))
    (.seq (.assign savedDelta (.mul (.var savedRow) (.var savedStride)))
      (.seq (.assign savedBasisDestination (.add (.var savedBank) (.var savedDelta)))
        (.assign savedChartDestination (.add (.var savedBasisDestination) (.var savedLane)))))

/-- Address the durable row from the current mode offset and archive cursor. -/
theorem addressChart_run (F : FieldPresentation K) {B Sn base lane offset i : ℕ} {s : Env}
    (hs : Slots F canonical qN.WS Sn B s) (hOffset : s.vars savedOffset=offset)
    (hBank : s.vars savedBank=base) (hLane : s.vars savedLane=lane)
    (hStride : s.vars savedStride=2*lane) (hIndex : s.vars cursor=i)
    (hiB : i<B) (hRowB : offset+i<B) (hStrideB : 2*lane<B)
    (hBound : rowChart base lane (offset+i)<B) :
    ∃ t, Run B addressChart s t 16 ∧ Slots F canonical qN.WS Sn B t ∧
      t.vars savedRow=offset+i ∧ t.vars savedBasisDestination=rowBasis base lane (offset+i) ∧
      t.vars savedChartDestination=rowChart base lane (offset+i) ∧
      (∀ k, val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      t.arrs=s.arrs ∧ Frame addressChart s t := by
  let row := offset+i
  let delta := row*(2*lane)
  let dst := base+delta
  let u := s.setVar savedRow row
  let v := u.setVar savedDelta delta
  let w := v.setVar savedBasisDestination dst
  let t := w.setVar savedChartDestination (dst+lane)
  have hb : dst+lane<B := hBound
  have hRow : row<B := hRowB
  have hDelta : delta<B := by omega
  have hDst : dst<B := by omega
  have r₀ : Run B (.assign savedRow (.add (.var savedOffset) (.var cursor))) s u 4 :=
    Run.assign (ev_add (ev_var hOffset (by omega)) (ev_var hIndex hiB) hRowB)
  have r₁ : Run B (.assign savedDelta (.mul (.var savedRow) (.var savedStride))) u v 4 :=
    Run.assign (ev_mul (ev_var (by simp [u]) hRow)
      (ev_var (by simp [u,show savedStride≠savedRow by decide,hStride]) hStrideB) hDelta)
  have r₂ : Run B (.assign savedBasisDestination (.add (.var savedBank) (.var savedDelta))) v w 4 :=
    Run.assign (ev_add (ev_var (by simp [v,u,show savedBank≠savedDelta by decide,
      show savedBank≠savedRow by decide,hBank]) (by omega))
      (ev_var (by simp [v]) hDelta) hDst)
  have r₃ : Run B (.assign savedChartDestination (.add (.var savedBasisDestination) (.var savedLane))) w t 4 :=
    Run.assign (ev_add (ev_var (by simp [w]) hDst)
      (ev_var (by simp [w,v,u,show savedLane≠savedBasisDestination by decide,
        show savedLane≠savedDelta by decide,show savedLane≠savedRow by decide,hLane])
        (by omega)) hb)
  have rt : Run B addressChart s t 16 := r₀.seq (r₁.seq (r₂.seq r₃))
  have hU : Slots F canonical qN.WS Sn B u := Slots.setVar F canonical hs (by decide) (by decide) _
  have hV : Slots F canonical qN.WS Sn B v := Slots.setVar F canonical hU (by decide) (by decide) _
  have hW : Slots F canonical qN.WS Sn B w := Slots.setVar F canonical hV (by decide) (by decide) _
  have hT : Slots F canonical qN.WS Sn B t := Slots.setVar F canonical hW (by decide) (by decide) _
  refine ⟨t,rt,hT,?_,?_,by simp [t,rowChart,rowBasis,dst,delta,row],?_,rfl,Frame.of_run rt⟩
  · simp [t,w,v,u,row,show savedRow≠savedChartDestination by decide,
      show savedRow≠savedBasisDestination by decide,show savedRow≠savedDelta by decide]
  · simp [t,w,rowBasis,dst,delta,row,show savedBasisDestination≠savedChartDestination by decide]
  · intro k
    rw [show t=w.setVar savedChartDestination (dst+lane) from rfl,
      val_setVar F canonical (by decide),show w=v.setVar savedBasisDestination dst from rfl,
      val_setVar F canonical (by decide),show v=u.setVar savedDelta delta from rfl,
      val_setVar F canonical (by decide),show u=s.setVar savedRow row from rfl,
      val_setVar F canonical (by decide)]

theorem rowChart_end_le_next (base lane : ℕ) {r q : ℕ} (h : r < q) :
    rowChart base lane r+lane ≤ rowBasis base lane q := by
  have hc := Nat.mul_le_mul_right (2*lane) (Nat.succ_le_iff.mpr h)
  rw [Nat.succ_mul] at hc
  unfold rowChart rowBasis
  omega

end EvenTI.P20Sweep
