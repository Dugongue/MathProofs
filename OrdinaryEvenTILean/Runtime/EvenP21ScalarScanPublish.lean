import EvenP21ScalarScanSelect

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000

namespace EvenTI.P21ScalarScan

open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_mul ev_var)
open Mathproof.Problem18PairLargeBank20261004 (copyBlock copyBlock_run Clean)
open Mathproof.Problem18ClaudeIMPSlots20261001 (NoVar)
open Mathproof.Problem18PairLargeWords20261004 (wcSrc wcDst wcCnt)

def storeSelectorHead (j : ℕ) (word : String) : Com :=
  .store selectorHeaderBank (.add (.mul (.lit 4) (.var scanModeCursor)) (.lit j)) (.var word)

def publishScanModeHeads : Com :=
  .seq (storeSelectorHead 0 stencilLimit) (.seq (storeSelectorHead 1 stencilColumns)
    (.seq (storeSelectorHead 2 stencilZero) (storeSelectorHead 3 stencilReference)))

def publishScanModeSlice (src dst cap : String) : Com :=
  copyBlock src dst (.lit 0) (.mul (.var scanModeCursor) (.var cap)) (.var cap)

def publishScanMode : Com :=
  .seq publishScanModeHeads
    (.seq (publishScanModeSlice stencilChartBank selectorChartTable selectorChartCapacity)
      (publishScanModeSlice stencilSitesBank selectorSitesTable selectorSitesCapacity))

private theorem storeSelectorHead_run {W i j v : ℕ} {u s : Env} {word : String} {heads : ℕ → ℕ}
    (hW : 4 < W) (hiW : i < W) (hj : j < 4)
    (hi : u.vars scanModeCursor = i) (hV : u.vars word = v) (hvW : v < W)
    (hFit : 4*i+j < (u.arrs selectorHeaderBank).length) (hLen : (u.arrs selectorHeaderBank).length < W)
    (seg : SegInv (s.arrs selectorHeaderBank) (u.arrs selectorHeaderBank) (4*i) j heads)
    (hSem : v = heads j) :
    ∃ t, Run W (storeSelectorHead j word) u t 7 ∧ Frame (storeSelectorHead j word) u t ∧
      SegInv (s.arrs selectorHeaderBank) (t.arrs selectorHeaderBank) (4*i) (j+1) heads := by
  have prod := ev_mul (evalB_lit hW) (ev_var hi hiW) (show 4*i < W by omega)
  have address := ev_add prod (evalB_lit (hj.trans hW)) (hFit.trans hLen)
  let t := u.setArr selectorHeaderBank (4*i+j) v
  have rr : Run W (storeSelectorHead j word) u t 7 := Run.store address (ev_var hV hvW) hFit
  refine ⟨t,rr,Frame.of_run rr,?_⟩
  simpa [t,arrs_setArr] using seg.step hFit hSem

theorem publishScanModeHeads_run {W n i : ℕ} {s : Env} (p : ScanModeInput W n)
    (hW : 4 < W) (hiW : i < W) (hIndex : s.vars scanModeCursor = i)
    (hFit : 4*i+4 ≤ (s.arrs selectorHeaderBank).length) (hLen : (s.arrs selectorHeaderBank).length < W)
    (hL : s.vars stencilLimit=p.L) (hC : s.vars stencilColumns=p.columns)
    (hZ : s.vars stencilZero=p.zero) (hR : s.vars stencilReference=p.reference.val)
    (hRef : p.reference.val < W) :
    ∃ t, Run W publishScanModeHeads s t 28 ∧ Frame publishScanModeHeads s t ∧
      SegInv (s.arrs selectorHeaderBank) (t.arrs selectorHeaderBank) (4*i) 4
        (fun j => [p.L,p.columns,p.zero,p.reference.val].getD j 0) := by
  let heads := fun j => [p.L,p.columns,p.zero,p.reference.val].getD j 0
  obtain ⟨u,r0,f0,seg0⟩ := storeSelectorHead_run (j:=0) hW hiW (by decide) hIndex hL p.wordL
    (by omega) hLen (SegInv.zero _ _ heads) rfl
  have huFit : 4*i+4 ≤ (u.arrs selectorHeaderBank).length := by rw [f0.len]; exact hFit
  have huLen : (u.arrs selectorHeaderBank).length < W := (f0.len _).trans_lt hLen
  obtain ⟨v,r1,f1,seg1⟩ := storeSelectorHead_run (j:=1) hW hiW (by decide)
    ((f0.vars _ (by decide)).trans hIndex) ((f0.vars _ (by decide)).trans hC) p.wordColumns
    (by omega) huLen seg0 rfl
  have hvFit : 4*i+4 ≤ (v.arrs selectorHeaderBank).length := by rw [f1.len]; exact huFit
  have hvLen : (v.arrs selectorHeaderBank).length < W := (f1.len _).trans_lt huLen
  obtain ⟨z,r2,f2,seg2⟩ := storeSelectorHead_run (j:=2) hW hiW (by decide)
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hIndex))
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hZ)) p.wordZero
    (by omega) hvLen seg1 rfl
  have hzFit : 4*i+4 ≤ (z.arrs selectorHeaderBank).length := by rw [f2.len]; exact hvFit
  have hzLen : (z.arrs selectorHeaderBank).length < W := (f2.len _).trans_lt hvLen
  obtain ⟨t,r3,_,seg3⟩ := storeSelectorHead_run (j:=3) hW hiW (by decide)
    ((f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hIndex)))
    ((f2.vars _ (by decide)).trans ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hR))) hRef
    (by omega) hzLen seg2 rfl
  have rr : Run W publishScanModeHeads s t 28 := r0.seq (r1.seq (r2.seq r3))
  exact ⟨t,rr,Frame.of_run rr,seg3⟩

private theorem publishScanModeSlice_run {W i cap : ℕ} {s : Env} (src dst capReg : String)
    (hSD : src ≠ dst) (hClean : Clean (.mul (.var scanModeCursor) (.var capReg)) ∧ Clean (.var capReg))
    (hOne : 1 < W) (hi : s.vars scanModeCursor = i) (hiW : i < W)
    (hc : s.vars capReg=cap) (hcW : cap < W)
    (hSource : (s.arrs src).length = cap) (hFit : i*cap+cap ≤ (s.arrs dst).length)
    (hTarget : (s.arrs dst).length < W) (hWords : ∀ v ∈ s.arrs src, v < W) :
    ∃ t, Run W (publishScanModeSlice src dst capReg) s t (20*cap+18) ∧
      Frame (publishScanModeSlice src dst capReg) s t ∧
      SegInv (s.arrs dst) (t.arrs dst) (i*cap) cap (fun k => (s.arrs src).getD k 0) := by
  have ec := ev_var hc hcW
  have ed := ev_mul (ev_var hi hiW) ec (by omega)
  have hSourceWords (j : ℕ) (hj : j < cap) : (s.arrs src).getD (0+j) 0 < W := by
    have hj' : j < (s.arrs src).length := hSource.symm ▸ hj
    rw [Nat.zero_add,List.getD_eq_getElem _ _ hj']
    exact hWords _ (List.getElem_mem hj')
  obtain ⟨t,hr,_,_,_,vals,_,_⟩ := copyBlock_run src dst hSD s (by simp [Clean,NoVar] : Clean (.lit 0))
    hClean.1 hClean.2 (evalB_lit (by omega)) ed ec (by omega) hFit (by rwa [hSource]) hTarget hSourceWords hOne
  have rr : Run W (publishScanModeSlice src dst capReg) s t (20*cap+18) := hr
  refine ⟨t,rr,Frame.of_run rr,?_⟩
  constructor
  · intro j hj
    rw [vals,if_pos ⟨by omega,by omega⟩,Nat.add_sub_cancel_left,Nat.zero_add]
  · intro j hj
    rw [vals,if_neg (by omega)]

/-- Write a live mode's literal headers and native chart/site words to its
unique durable record. Every other mode's records retain their old contents. -/
theorem publishScanMode_run {W n i c d : ℕ} {s : Env} (p : ScanModeInput W n)
    (hW : 4 < W) (hiW : i < W) (hIndex : s.vars scanModeCursor = i)
    (hHeaderFit : 4*i+4 ≤ (s.arrs selectorHeaderBank).length)
    (hHeaderWord : (s.arrs selectorHeaderBank).length < W)
    (hL : s.vars stencilLimit=p.L) (hC : s.vars stencilColumns=p.columns)
    (hZ : s.vars stencilZero=p.zero) (hR : s.vars stencilReference=p.reference.val) (hRef : p.reference.val < W)
    (hChart : s.arrs stencilChartBank=p.chart) (hChartLength : p.chart.length=c)
    (hSites : s.arrs stencilSitesBank=p.sites) (hSiteLength : p.sites.length=d)
    (hc : s.vars selectorChartCapacity=c) (hd : s.vars selectorSitesCapacity=d)
    (hcW : c < W) (hdW : d < W)
    (hChartFit : i*c+c ≤ (s.arrs selectorChartTable).length) (hChartWord : (s.arrs selectorChartTable).length < W)
    (hSitesFit : i*d+d ≤ (s.arrs selectorSitesTable).length) (hSitesWord : (s.arrs selectorSitesTable).length < W) :
    ∃ t, Run W publishScanMode s t (20*c+20*d+64) ∧ Frame publishScanMode s t ∧
      SegInv (s.arrs selectorHeaderBank) (t.arrs selectorHeaderBank) (4*i) 4
        (fun j => [p.L,p.columns,p.zero,p.reference.val].getD j 0) ∧
      SegInv (s.arrs selectorChartTable) (t.arrs selectorChartTable) (i*c) c (fun j => p.chart.getD j 0) ∧
      SegInv (s.arrs selectorSitesTable) (t.arrs selectorSitesTable) (i*d) d (fun j => p.sites.getD j 0) := by
  have hOne : 1 < W := by omega
  obtain ⟨u,r0,f0,heads⟩ := publishScanModeHeads_run p hW hiW hIndex hHeaderFit hHeaderWord hL hC hZ hR hRef
  have uChart : u.arrs stencilChartBank=p.chart := (f0.arrs _ (by decide)).trans hChart
  obtain ⟨v,r1,f1,hChartSeg⟩ := publishScanModeSlice_run stencilChartBank selectorChartTable
    selectorChartCapacity (by decide) (by simp [Clean,NoVar,scanModeCursor,selectorChartCapacity,wcSrc,wcDst,wcCnt]) hOne ((f0.vars _ (by decide)).trans hIndex) hiW
    ((f0.vars _ (by decide)).trans hc) hcW (by rw [uChart,hChartLength])
    (by rw [f0.len]; exact hChartFit) ((f0.len _).trans_lt hChartWord) (by rw [uChart]; exact p.wordChart)
  have vSites : v.arrs stencilSitesBank=p.sites := (f1.arrs _ (by decide)).trans ((f0.arrs _ (by decide)).trans hSites)
  obtain ⟨t,r2,f2,hSitesSeg⟩ := publishScanModeSlice_run stencilSitesBank selectorSitesTable
    selectorSitesCapacity (by decide) (by simp [Clean,NoVar,scanModeCursor,selectorSitesCapacity,wcSrc,wcDst,wcCnt]) hOne
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hIndex)) hiW
    ((f1.vars _ (by decide)).trans ((f0.vars _ (by decide)).trans hd)) hdW (by rw [vSites,hSiteLength])
    (by rw [f1.len,f0.len]; exact hSitesFit) ((f1.len _).trans_lt ((f0.len _).trans_lt hSitesWord))
    (by rw [vSites]; exact p.wordSites)
  have rr : Run W publishScanMode s t (20*c+20*d+64) := (r0.seq (r1.seq r2)).mono (by omega)
  refine ⟨t,rr,Frame.of_run rr,?_,?_,?_⟩
  · rw [f2.arrs _ (by decide),f1.arrs _ (by decide)]
    exact heads
  · rw [f2.arrs _ (by decide)]
    simpa only [f0.arrs selectorChartTable (by decide),uChart] using hChartSeg
  · simpa only [f1.arrs selectorSitesTable (by decide),f0.arrs selectorSitesTable (by decide),vSites] using hSitesSeg

#print axioms publishScanModeHeads_run
#print axioms publishScanMode_run
end EvenTI.P21ScalarScan
