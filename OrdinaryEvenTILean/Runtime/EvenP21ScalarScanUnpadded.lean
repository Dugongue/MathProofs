import EvenP21ScalarScanSelect
import EvenP20ScalarPositiveSites

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1000000

namespace EvenTI.P21ScalarScan

open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P20Scalar (positiveSiteCount)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18PairLargeBank20261004 (zeroBlock zeroBlock_run wcRegs Clean)
open Mathproof.Problem18PairLargeWords20261004 (wcIdx wcSrc wcDst wcCnt)

def chooseUnpaddedReference : Com :=
  .ite (.lt (.lit 0) (.var stencilLimit))
    (.assign stencilReference (.get stencilSitesBank (.lit 0)))
    (.assign stencilReference (.lit 0))

def prepareUnpaddedMode : Com :=
  .seq (zeroBlock stencilChartBank (.lit 0) (.var selectorChartCapacity))
    (.seq (.assign stencilLimit (.var positiveSiteCount))
      (.seq (.assign stencilColumns (.lit 1))
        (.seq (.assign stencilZero (.lit 1)) chooseUnpaddedReference)))

/-- Install an ordinary mode's full support and reference from its actual native sites. -/
theorem prepareUnpaddedMode_run {W L c : ℕ} {s : Env} (sites : List ℕ)
    (hOne : 1 < W) (hc : c < W) (hL : L < W)
    (hLimit : s.vars positiveSiteCount=L) (hCapacity : s.vars selectorChartCapacity=c)
    (hChart : (s.arrs stencilChartBank).length=c)
    (hSite : s.arrs stencilSitesBank=sites) (hFit : L ≤ sites.length)
    (hWords : ∀ a ∈ sites, a < W) :
    ∃ t, Run W prepareUnpaddedMode s t (20*c+28) ∧ Frame prepareUnpaddedMode s t ∧
      t.vars stencilLimit=L ∧ t.vars stencilColumns=1 ∧ t.vars stencilZero=1 ∧
      t.vars stencilReference=(if 0 < L then sites.getD 0 0 else 0) ∧
      t.arrs stencilChartBank=List.replicate c 0 ∧ t.arrs stencilSitesBank=sites := by
  obtain ⟨u,r0,huReg,huOther,huLen,huWord,_,_⟩ := zeroBlock_run stencilChartBank s
    (by change Clean (.var selectorChartCapacity); simp [Clean,NoVar,selectorChartCapacity,wcSrc,wcDst,wcCnt]) (evalB_lit (by omega : 0 < W))
    (ev_var hCapacity hc) (by omega) (by rwa [hChart]) hOne
  have rr0 : Run W (zeroBlock stencilChartBank (.lit 0) (.var selectorChartCapacity)) s u (20*c+14) := r0
  have hUC : u.vars positiveSiteCount=L :=
    (huReg _ (by simp [wcRegs,wcIdx,wcSrc,wcDst,wcCnt,positiveSiteCount])).trans hLimit
  have hChartU : u.arrs stencilChartBank=List.replicate c 0 := by
    apply List.ext_getElem (by rw [huLen,hChart,List.length_replicate])
    intro k hk hk'
    rw [← List.getD_eq_getElem _ 0 hk,huWord,List.getElem_replicate]
    have : k < c := by simpa using hk'
    simp [this]
  have hSitesU : u.arrs stencilSitesBank=sites := (huOther _ (by decide)).trans hSite
  let u₁ := u.setVar stencilLimit L
  let u₂ := u₁.setVar stencilColumns 1
  let v := u₂.setVar stencilZero 1
  have r1 : Run W (.assign stencilLimit (.var positiveSiteCount)) u u₁ 2 := Run.assign (ev_var hUC hL)
  have r2 : Run W (.assign stencilColumns (.lit 1)) u₁ u₂ 2 := Run.assign (evalB_lit hOne)
  have r3 : Run W (.assign stencilZero (.lit 1)) u₂ v 2 := Run.assign (evalB_lit hOne)
  have vLimit : v.vars stencilLimit=L := by
    simp [v,u₂,u₁,show stencilLimit ≠ stencilColumns by decide,show stencilLimit ≠ stencilZero by decide]
  have vColumns : v.vars stencilColumns=1 := by simp [v,u₂,show stencilColumns ≠ stencilZero by decide]
  have vZero : v.vars stencilZero=1 := by simp [v]
  have eCount : (Expr.var stencilLimit).evalB W v=some L := ev_var vLimit hL
  let reference := if 0 < L then sites.getD 0 0 else 0
  let t := v.setVar stencilReference reference
  have r4 : Run W chooseUnpaddedReference v t 8 := by
    by_cases hPos : 0 < L
    · have hAt : 0 < sites.length := hPos.trans_le hFit
      have hWord : sites.getD 0 0 < W := by
        rw [List.getD_eq_getElem _ _ hAt]
        exact hWords _ (List.getElem_mem hAt)
      have get : (Expr.get stencilSitesBank (.lit 0)).evalB W v=some (sites.getD 0 0) := by
        apply evalB_get (evalB_lit (by omega : 0 < W)) _ hWord
        change (u.arrs stencilSitesBank)[0]? = some (sites.getD 0 0)
        rw [hSitesU,List.getElem?_eq_getElem hAt,List.getD_eq_getElem _ _ hAt]
      have guard : (Cond.lt (.lit 0) (.var stencilLimit)).evalB W v=some true := by
        simpa only [hPos,decide_true] using evalB_condLt (evalB_lit (by omega : 0 < W)) eCount
      simpa [t,reference,hPos,chooseUnpaddedReference] using
        (Run.ite_true (d:=.assign stencilReference (.lit 0)) guard (Run.assign (x:=stencilReference) get)).mono
          (by decide : 4+3 ≤ 8)
    · have guard : (Cond.lt (.lit 0) (.var stencilLimit)).evalB W v=some false := by
        simpa only [hPos,decide_false] using evalB_condLt (evalB_lit (by omega : 0 < W)) eCount
      simpa [t,reference,hPos,chooseUnpaddedReference] using
        (Run.ite_false (c:=.assign stencilReference (.get stencilSitesBank (.lit 0))) guard
          (Run.assign (x:=stencilReference) (evalB_lit (by omega : 0 < W)))).mono (by decide : 4+2 ≤ 8)
  have rr : Run W prepareUnpaddedMode s t (20*c+28) := (rr0.seq (r1.seq (r2.seq (r3.seq r4)))).mono (by omega)
  refine ⟨t,rr,Frame.of_run rr,?_,?_,?_,by simp [t,reference],hChartU,hSitesU⟩
  · simpa [t,show stencilLimit ≠ stencilReference by decide] using vLimit
  · simpa [t,show stencilColumns ≠ stencilReference by decide] using vColumns
  · simpa [t,show stencilZero ≠ stencilReference by decide] using vZero

#print axioms prepareUnpaddedMode_run
end EvenTI.P21ScalarScan
