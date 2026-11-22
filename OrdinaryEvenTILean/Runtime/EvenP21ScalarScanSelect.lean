import EvenP21ScalarScanModes
import Mathproof.Meta.Problem18P34AssemblyMatrixGatherSetup20261003

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1300000

namespace EvenTI.P21ScalarScan

open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (commands commands_run install)
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_mul ev_var)
open Mathproof.Problem18PairLargeBank20261004 (copyBlock copyBlock_run Clean)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18PairLargeWords20261004 (wcSrc wcDst wcCnt)

def selectorHeaderBank : String := "even.p21.scalar.select.headers"
def selectorChartTable : String := "even.p21.scalar.select.charts"
def selectorSitesTable : String := "even.p21.scalar.select.sites"
def selectorChartCapacity : String := "even.p21.scalar.select.chart_capacity"
def selectorSitesCapacity : String := "even.p21.scalar.select.sites_capacity"

def selectorHeaderRead (j : ℕ) : Expr :=
  .get selectorHeaderBank (.add (.mul (.lit 4) (.var scanModeCursor)) (.lit j))

def selectorHeadCommands : List (String × Expr) :=
  [(stencilLimit,selectorHeaderRead 0), (stencilColumns,selectorHeaderRead 1),
   (stencilZero,selectorHeaderRead 2), (stencilReference,selectorHeaderRead 3)]

def installSelectorHeads : Com := commands selectorHeadCommands

def copySelectedChart (src dst cap : String) : Com :=
  copyBlock src dst (.mul (.var scanModeCursor) (.var cap)) (.lit 0) (.var cap)

def prepareSelectedScanMode : Com :=
  .seq installSelectorHeads
    (.seq (copySelectedChart selectorChartTable stencilChartBank selectorChartCapacity)
      (copySelectedChart selectorSitesTable stencilSitesBank selectorSitesCapacity))

/-- Physical selected-mode records read by the scalar caller. Each table has
uniform capacity, independent of the active shape stored in its mode header. -/
structure SelectorData {W modes n : ℕ} (plan : Fin modes → ScanModeInput W n)
    (chartCapacity siteCapacity : ℕ) (s : Env) : Prop where
  headerFit : 4*modes ≤ (s.arrs selectorHeaderBank).length
  headerWord : (s.arrs selectorHeaderBank).length < W
  header : ∀ (i : Fin modes) (j : Fin 4), (s.arrs selectorHeaderBank).getD (4*i.val+j.val) 0 =
    ([ (plan i).L, (plan i).columns, (plan i).zero, (plan i).reference.val ]).getD j.val 0
  chartsFit : modes*chartCapacity ≤ (s.arrs selectorChartTable).length
  chartsWord : (s.arrs selectorChartTable).length < W
  charts : ∀ (i : Fin modes) k, k < chartCapacity →
    (s.arrs selectorChartTable).getD (i.val*chartCapacity+k) 0 = (plan i).chart.getD k 0
  chartCapacityWord : chartCapacity < W
  chartCapacityReg : s.vars selectorChartCapacity = chartCapacity
  chartLengths : ∀ i, (plan i).chart.length = chartCapacity
  chartTarget : (s.arrs stencilChartBank).length = chartCapacity
  sitesFit : modes*siteCapacity ≤ (s.arrs selectorSitesTable).length
  sitesWord : (s.arrs selectorSitesTable).length < W
  sites : ∀ (i : Fin modes) k, k < siteCapacity →
    (s.arrs selectorSitesTable).getD (i.val*siteCapacity+k) 0 = (plan i).sites.getD k 0
  siteCapacityWord : siteCapacity < W
  siteCapacityReg : s.vars selectorSitesCapacity = siteCapacity
  siteLengths : ∀ i, (plan i).sites.length = siteCapacity
  siteTarget : (s.arrs stencilSitesBank).length = siteCapacity

theorem installSelectorHeads_run {W modes n : ℕ} {s : Env}
    (plan : Fin modes → ScanModeInput W n) {c d : ℕ}
    (h : SelectorData plan c d s) (i : Fin modes) (hi : s.vars scanModeCursor=i.val)
    (hReference : (plan i).reference.val < W) :
    ∃ t, Run W installSelectorHeads s t 33 ∧ Frame installSelectorHeads s t ∧
      t.vars stencilLimit=(plan i).L ∧ t.vars stencilColumns=(plan i).columns ∧
      t.vars stencilZero=(plan i).zero ∧ t.vars stencilReference=(plan i).reference.val := by
  let p := plan i
  let vals := [p.L,p.columns,p.zero,p.reference.val]
  have hI : i.val < W := by have := i.isLt; have := h.headerFit; have := h.headerWord; omega
  have hi4 : 4*i.val < W := by have := i.isLt; have := h.headerFit; have := h.headerWord; omega
  have h4 : 4 < W := by have := i.isLt; have := h.headerFit; have := h.headerWord; omega
  have er (j : Fin 4) (v : ℕ) (hv : vals.getD j.val 0 = v) (hV : v < W) :
      (selectorHeaderRead j.val).evalB W s = some v := by
    have hj : 4*i.val+j.val < (s.arrs selectorHeaderBank).length := by
      have := i.isLt
      have := j.isLt
      have := h.headerFit
      omega
    have ex : (Expr.mul (.lit 4) (.var scanModeCursor)).evalB W s=some (4*i.val) :=
      ev_mul (evalB_lit h4) (ev_var hi hI) hi4
    have e := ev_add ex (evalB_lit (j.isLt.trans h4)) (hj.trans h.headerWord)
    unfold selectorHeaderRead
    apply evalB_get e _ hV
    rw [List.getElem?_eq_getElem hj,← List.getD_eq_getElem _ _ hj,h.header i j,hv]
  have evals : List.Forall₂ (fun v w => v.2.evalB W s=some w) selectorHeadCommands vals := by
    simp only [selectorHeadCommands, vals, List.forall₂_cons]
    exact ⟨er 0 _ rfl p.wordL,er 1 _ rfl p.wordColumns,er 2 _ rfl p.wordZero,
      er 3 _ rfl hReference,List.Forall₂.nil⟩
  let pairs := List.zip (selectorHeadCommands.map Prod.fst) vals
  let t := install pairs s
  have rr := commands_run selectorHeadCommands vals s rfl evals (by
    intro x hx y hy
    simp only [selectorHeadCommands,List.mem_cons,List.not_mem_nil,or_false] at hx hy
    rcases hx with rfl|rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl|rfl <;>
      simp [NoVar,selectorHeaderRead,scanModeCursor,stencilLimit,stencilColumns,stencilZero,stencilReference])
  have rt : Run W installSelectorHeads s t 33 := rr.mono (by decide)
  refine ⟨t,rt,Frame.of_run rt,?_,?_,?_,?_⟩ <;>
    simp [t,pairs,vals,selectorHeadCommands,install,stencilLimit,stencilColumns,stencilZero,stencilReference,p]

private theorem copySelectedChart_run {W cap i : ℕ} {s : Env}
    (src dst capReg : String) (hSD : src ≠ dst)
    (hClean : Clean (.mul (.var scanModeCursor) (.var capReg)) ∧ Clean (.var capReg))
    (words : List ℕ) (hLength : words.length = cap) (hValues : ∀ a ∈ words, a < W)
    (hCap : s.vars capReg = cap) (hIndex : s.vars scanModeCursor = i)
    (hIW : i < W) (hCapW : cap < W) (hOne : 1 < W)
    (hFit : i*cap+cap ≤ (s.arrs src).length) (hSrc : (s.arrs src).length < W)
    (hDst : (s.arrs dst).length = cap)
    (hInput : ∀ k < cap, (s.arrs src).getD (i*cap+k) 0 = words.getD k 0) :
    ∃ t, Run W (copySelectedChart src dst capReg) s t (20*cap+18) ∧
      Frame (copySelectedChart src dst capReg) s t ∧ t.arrs dst=words := by
  have ec := ev_var hCap hCapW
  have es := ev_mul (ev_var hIndex hIW) ec (by omega)
  have hPay (k : ℕ) (hk : k < cap) : (s.arrs src).getD (i*cap+k) 0 < W := by
    have hKW : k < words.length := by omega
    rw [hInput k hk,List.getD_eq_getElem _ _ hKW]
    exact hValues _ (List.getElem_mem hKW)
  obtain ⟨t,r,_,_,hl,hWord,_,_⟩ := copyBlock_run src dst hSD s hClean.1
    (by simp [Clean,NoVar] : Clean (.lit 0)) hClean.2 es (evalB_lit (by omega)) ec hFit
    (by omega) hSrc (by rwa [hDst]) hPay hOne
  have rr : Run W (copySelectedChart src dst capReg) s t (20*cap+18) := r
  refine ⟨t,rr,Frame.of_run rr,?_⟩
  apply List.ext_getElem (hl.trans (hDst.trans hLength.symm))
  intro k ht hw
  rw [← List.getD_eq_getElem _ 0 ht,← List.getD_eq_getElem _ 0 hw,hWord k]
  simp only [Nat.zero_le,true_and,Nat.zero_add,Nat.sub_zero,if_pos (show k < cap by omega)]
  exact hInput k (by omega)

theorem prepareSelectedScanMode_run {W modes n c d : ℕ} {s : Env}
    (plan : Fin modes → ScanModeInput W n) (h : SelectorData plan c d s)
    (i : Fin modes) (hi : s.vars scanModeCursor=i.val) (hOne : 1 < W)
    (hReference : (plan i).reference.val < W) :
    ∃ t, Run W prepareSelectedScanMode s t (20*c+20*d+69) ∧
      Frame prepareSelectedScanMode s t ∧
      t.vars stencilLimit=(plan i).L ∧ t.vars stencilColumns=(plan i).columns ∧
      t.vars stencilZero=(plan i).zero ∧ t.vars stencilReference=(plan i).reference.val ∧
      t.arrs stencilChartBank=(plan i).chart ∧ t.arrs stencilSitesBank=(plan i).sites := by
  have hI : i.val < W := by have := i.isLt; have := h.headerFit; have := h.headerWord; omega
  obtain ⟨u,r0,f0,hL,hC,hZ,hR⟩ := installSelectorHeads_run plan h i hi hReference
  obtain ⟨v,r1,f1,hChart⟩ := copySelectedChart_run
    selectorChartTable stencilChartBank selectorChartCapacity (by decide) (by simp [Clean,NoVar,scanModeCursor,selectorChartCapacity,wcSrc,wcDst,wcCnt])
    (plan i).chart (h.chartLengths i) (plan i).wordChart
    ((f0.vars _ (by decide)).trans h.chartCapacityReg) ((f0.vars _ (by decide)).trans hi)
    hI h.chartCapacityWord hOne
    ((f0.len _).symm ▸ ((by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right c i.isLt :
      i.val*c+c ≤ modes*c).trans h.chartsFit)) ((f0.len _).trans_lt h.chartsWord)
    ((f0.len _).trans h.chartTarget)
    (fun k hk => (congrArg (fun u => u.getD (i.val*c+k) 0) (f0.arrs _ (by decide))).trans (h.charts i k hk))
  obtain ⟨t,r2,f2,hSite⟩ := copySelectedChart_run
    selectorSitesTable stencilSitesBank selectorSitesCapacity (by decide) (by simp [Clean,NoVar,scanModeCursor,selectorSitesCapacity,wcSrc,wcDst,wcCnt])
    (plan i).sites (h.siteLengths i) (plan i).wordSites
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans h.siteCapacityReg))
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hi))
    hI h.siteCapacityWord hOne
    ((f1.len _).symm ▸ ((f0.len _).symm ▸ ((by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right d i.isLt :
      i.val*d+d ≤ modes*d).trans h.sitesFit))) ((f1.len _).trans_lt ((f0.len _).trans_lt h.sitesWord))
    ((f1.len _).trans ((f0.len _).trans h.siteTarget))
    (fun k hk => (congrArg (fun u => u.getD (i.val*d+k) 0)
      ((f1.arrs _ (by decide)).trans (f0.arrs _ (by decide)))).trans (h.sites i k hk))
  have rr : Run W prepareSelectedScanMode s t (20*c+20*d+69) :=
    (r0.seq (r1.seq r2)).mono (by omega)
  exact ⟨t,rr,Frame.of_run rr, (f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans hL),
    (f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans hC),
    (f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans hZ),
    (f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans hR),
    (f2.arrs _ (by decide)).trans hChart,hSite⟩

#print axioms installSelectorHeads_run
#print axioms prepareSelectedScanMode_run
end EvenTI.P21ScalarScan
