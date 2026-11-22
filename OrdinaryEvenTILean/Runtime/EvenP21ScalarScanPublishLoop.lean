import EvenP21ScalarScanPublish
import Mathproof.Meta.Problem18PairLargeFinalLoop20261004

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1600000

namespace EvenTI.P21ScalarScan

open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop forLoop_run)

structure SelectorTableLayout {W modes n : ℕ} (plan : Fin modes → ScanModeInput W n)
    (c d : ℕ) (s : Env) : Prop where
  headerFit : 4*modes ≤ (s.arrs selectorHeaderBank).length
  headerWord : (s.arrs selectorHeaderBank).length < W
  chartFit : modes*c ≤ (s.arrs selectorChartTable).length
  chartWord : (s.arrs selectorChartTable).length < W
  chartCapacityWord : c < W
  chartCapacityReg : s.vars selectorChartCapacity = c
  chartLengths : ∀ i, (plan i).chart.length = c
  chartTarget : (s.arrs stencilChartBank).length = c
  siteFit : modes*d ≤ (s.arrs selectorSitesTable).length
  siteWord : (s.arrs selectorSitesTable).length < W
  siteCapacityWord : d < W
  siteCapacityReg : s.vars selectorSitesCapacity = d
  siteLengths : ∀ i, (plan i).sites.length = d
  siteTarget : (s.arrs stencilSitesBank).length = d

private theorem SelectorTableLayout.ofFrame {W modes n c d : ℕ} {s t : Env} {cmd : Com}
    {plan : Fin modes → ScanModeInput W n} (h : SelectorTableLayout plan c d s) (f : Frame cmd s t)
    (hc : selectorChartCapacity ∉ scalarWrites cmd) (hd : selectorSitesCapacity ∉ scalarWrites cmd) :
    SelectorTableLayout plan c d t := by
  exact ⟨(f.len _).symm ▸ h.headerFit,(f.len _).trans_lt h.headerWord,
    (f.len _).symm ▸ h.chartFit,(f.len _).trans_lt h.chartWord,h.chartCapacityWord,
    (f.vars _ hc).trans h.chartCapacityReg,h.chartLengths,(f.len _).trans h.chartTarget,
    (f.len _).symm ▸ h.siteFit,(f.len _).trans_lt h.siteWord,h.siteCapacityWord,
    (f.vars _ hd).trans h.siteCapacityReg,h.siteLengths,(f.len _).trans h.siteTarget⟩

private theorem SelectorTableLayout.setCursor {W modes n c d k : ℕ} {s : Env}
    {plan : Fin modes → ScanModeInput W n} (h : SelectorTableLayout plan c d s) :
    SelectorTableLayout plan c d (s.setVar scanModeCursor k) :=
  ⟨h.headerFit,h.headerWord,h.chartFit,h.chartWord,h.chartCapacityWord,
    by simpa [show selectorChartCapacity ≠ scanModeCursor by decide] using h.chartCapacityReg,
    h.chartLengths,h.chartTarget,h.siteFit,h.siteWord,h.siteCapacityWord,
    by simpa [show selectorSitesCapacity ≠ scanModeCursor by decide] using h.siteCapacityReg,
    h.siteLengths,h.siteTarget⟩

structure ScanModeOutput {W n : ℕ} (p : ScanModeInput W n) (s : Env) : Prop where
  limit : s.vars stencilLimit = p.L
  columns : s.vars stencilColumns = p.columns
  zeroWord : s.vars stencilZero = p.zero
  reference : s.vars stencilReference = p.reference.val
  chart : s.arrs stencilChartBank = p.chart
  sites : s.arrs stencilSitesBank = p.sites

def StoredScanMode {W n : ℕ} (p : ScanModeInput W n) (i c d : ℕ) (s : Env) : Prop :=
  (∀ j : Fin 4, (s.arrs selectorHeaderBank).getD (4*i+j.val) 0 =
    [p.L,p.columns,p.zero,p.reference.val].getD j.val 0) ∧
  (∀ k < c, (s.arrs selectorChartTable).getD (i*c+k) 0 = p.chart.getD k 0) ∧
  (∀ k < d, (s.arrs selectorSitesTable).getD (i*d+k) 0 = p.sites.getD k 0)

private theorem StoredScanMode.ofFrame {W n i c d : ℕ} {s t : Env} {cmd : Com}
    {p : ScanModeInput W n} (h : StoredScanMode p i c d s) (f : Frame cmd s t)
    (hH : selectorHeaderBank ∉ arrayWrites cmd) (hC : selectorChartTable ∉ arrayWrites cmd)
    (hS : selectorSitesTable ∉ arrayWrites cmd) : StoredScanMode p i c d t := by
  unfold StoredScanMode at *
  rw [f.arrs _ hH,f.arrs _ hC,f.arrs _ hS]
  exact h

def publishAllScanModes (produce : Com) : Com :=
  forLoop scanModeCursor scanModeCount (.seq produce publishScanMode)

private theorem beforeSlice {i j c k : ℕ} (hij : i < j) (hk : k < c) : i*c+k < j*c := by
  calc
    i*c+k < (i+1)*c := by rw [Nat.succ_mul]; omega
    _ ≤ j*c := Nat.mul_le_mul_right _ hij

/-- Produce durable mode tables from physically computed mode outputs.
Every completed row survives later modes even when input chart widths differ. -/
theorem publishAllScanModes_run {W n modes c d T : ℕ} {s : Env}
    (plan : Fin modes → ScanModeInput W n) (produce : Com) (Ready : Env → Prop)
    (hW : 4 < W) (hn : n < W) (hModes : modes < W) (hCount : s.vars scanModeCount = modes)
    (hLayout : SelectorTableLayout plan c d s) (hReady : Ready s)
    (hCursorReady : ∀ u k, Ready u → Ready (u.setVar scanModeCursor k))
    (hAfter : ∀ u v, Ready u → Frame publishScanMode u v → Ready v)
    (hProdCur : scanModeCursor ∉ scalarWrites produce) (hProdCount : scanModeCount ∉ scalarWrites produce)
    (hProdC : selectorChartCapacity ∉ scalarWrites produce) (hProdD : selectorSitesCapacity ∉ scalarWrites produce)
    (hArchiveH : selectorHeaderBank ∉ arrayWrites produce)
    (hArchiveC : selectorChartTable ∉ arrayWrites produce)
    (hArchiveS : selectorSitesTable ∉ arrayWrites produce)
    (hProduce : ∀ (i : Fin modes) (u : Env), Ready u → u.vars scanModeCursor = i.val →
      ∃ v, Run W produce u v T ∧ ScanModeOutput (plan i) v ∧ Ready v) :
    ∃ t, Run W (publishAllScanModes produce) s t ((T+20*c+20*d+72)*modes+6) ∧
      Frame (publishAllScanModes produce) s t ∧ SelectorData plan c d t ∧ Ready t := by
  let I (k : ℕ) (u : Env) := SelectorTableLayout plan c d u ∧ Ready u ∧
    ∀ i : Fin modes, i.val < k → StoredScanMode (plan i) i.val c d u
  have init : I 0 (s.setVar scanModeCursor 0) := ⟨hLayout.setCursor,hCursorReady _ _ hReady,by simp⟩
  have step : ∀ k < modes, ∀ u, I k u → u.vars scanModeCursor=k → u.vars scanModeCount=modes →
      ∃ t, Run W (.seq produce publishScanMode) u t (T+(20*c+20*d+64)) ∧
        t.vars scanModeCursor=k ∧ t.vars scanModeCount=modes ∧ I (k+1) (t.setVar scanModeCursor (k+1)) := by
    intro k hk u hu hCursor hLimit
    let i : Fin modes := ⟨k,hk⟩
    let p := plan i
    obtain ⟨v,r0,out,hr⟩ := hProduce i u hu.2.1 hCursor
    have f0 := Frame.of_run r0
    have hv := hu.1.ofFrame f0 hProdC hProdD
    have hCfit : k*c+c ≤ (v.arrs selectorChartTable).length := by
      rw [← Nat.succ_mul]
      exact (Nat.mul_le_mul_right _ hk).trans hv.chartFit
    have hDfit : k*d+d ≤ (v.arrs selectorSitesTable).length := by
      rw [← Nat.succ_mul]
      exact (Nat.mul_le_mul_right _ hk).trans hv.siteFit
    obtain ⟨t,r1,f1,head,chart,site⟩ := publishScanMode_run p hW (hk.trans hModes)
      ((f0.vars _ hProdCur).trans hCursor) (by have := hv.headerFit; omega) hv.headerWord
      out.limit out.columns out.zeroWord out.reference (p.reference.isLt.trans hn)
      out.chart (hv.chartLengths i) out.sites (hv.siteLengths i)
      hv.chartCapacityReg hv.siteCapacityReg hv.chartCapacityWord hv.siteCapacityWord
      hCfit hv.chartWord hDfit hv.siteWord
    have r := r0.seq r1
    refine ⟨t,r,(f1.vars _ (by decide)).trans ((f0.vars _ hProdCur).trans hCursor),
      (f1.vars _ (by decide)).trans ((f0.vars _ hProdCount).trans hLimit),
      (hv.ofFrame f1 (by decide) (by decide)).setCursor,hCursorReady _ _ (hAfter _ _ hr f1),?_⟩
    intro j hj
    change StoredScanMode (plan j) j.val c d t
    by_cases same : j = i
    · subst j
      exact ⟨fun j => head.inside j.val j.isLt,chart.inside,site.inside⟩
    · have ne : j.val ≠ k := fun e => same (Fin.ext e)
      have early : j.val < k := by omega
      have old := (hu.2.2 j early).ofFrame f0 hArchiveH hArchiveC hArchiveS
      refine ⟨fun l => (head.outside _ (.inl (by have := l.isLt; omega))).trans (old.1 l),
        fun l hl => (chart.outside _ (.inl (beforeSlice early hl))).trans (old.2.1 l hl),
        fun l hl => (site.outside _ (.inl (beforeSlice early hl))).trans (old.2.2 l hl)⟩
  obtain ⟨t,r,ht,_⟩ := forLoop_run scanModeCursor scanModeCount (.seq produce publishScanMode)
    (by decide) I hCount hModes init step
  have rr : Run W (publishAllScanModes produce) s t ((T+20*c+20*d+72)*modes+6) := by
    have cost : T+(20*c+20*d+64)+8 = T+20*c+20*d+72 := by omega
    exact r.mono (by rw [cost])
  let L := ht.1
  have rows (i : Fin modes) := ht.2.2 i i.isLt
  exact ⟨t,rr,Frame.of_run rr,⟨L.headerFit,L.headerWord,fun i => (rows i).1,
    L.chartFit,L.chartWord,fun i => (rows i).2.1,L.chartCapacityWord,L.chartCapacityReg,L.chartLengths,L.chartTarget,
    L.siteFit,L.siteWord,fun i => (rows i).2.2,L.siteCapacityWord,L.siteCapacityReg,L.siteLengths,L.siteTarget⟩,ht.2.1⟩

#print axioms publishAllScanModes_run
end EvenTI.P21ScalarScan
