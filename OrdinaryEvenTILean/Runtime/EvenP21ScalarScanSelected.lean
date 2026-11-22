import EvenP21ScalarScanSelect

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2000000

namespace EvenTI.P21ScalarScan

open scoped Matrix
open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover
open EvenTI.P17Scalar (scalarProbeLimit activeSlotBank)
open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)

private theorem SelectorData.ofFrame {W modes n c d : ℕ} {s t : Env} {cmd : Com}
    {plan : Fin modes → ScanModeInput W n} (h : SelectorData plan c d s) (f : Frame cmd s t)
    (hH : selectorHeaderBank ∉ arrayWrites cmd) (hC : selectorChartTable ∉ arrayWrites cmd)
    (hS : selectorSitesTable ∉ arrayWrites cmd) (hc : selectorChartCapacity ∉ scalarWrites cmd)
    (hd : selectorSitesCapacity ∉ scalarWrites cmd) : SelectorData plan c d t := by
  constructor
  · rw [f.len _]; exact h.headerFit
  · rw [f.len _]; exact h.headerWord
  · rw [f.arrs _ hH]; exact h.header
  · rw [f.len _]; exact h.chartsFit
  · rw [f.len _]; exact h.chartsWord
  · rw [f.arrs _ hC]; exact h.charts
  · exact h.chartCapacityWord
  · exact (f.vars _ hc).trans h.chartCapacityReg
  · exact h.chartLengths
  · exact (f.len _).trans h.chartTarget
  · rw [f.len _]; exact h.sitesFit
  · rw [f.len _]; exact h.sitesWord
  · rw [f.arrs _ hS]; exact h.sites
  · exact h.siteCapacityWord
  · exact (f.vars _ hd).trans h.siteCapacityReg
  · exact h.siteLengths
  · exact (f.len _).trans h.siteTarget

private theorem SelectorData.setVar {W modes n c d : ℕ} {s : Env}
    {plan : Fin modes → ScanModeInput W n} (h : SelectorData plan c d s) (r : String) (k : ℕ)
    (hc : selectorChartCapacity ≠ r) (hd : selectorSitesCapacity ≠ r) :
    SelectorData plan c d (s.setVar r k) :=
  ⟨h.headerFit,h.headerWord,h.header,h.chartsFit,h.chartsWord,h.charts,h.chartCapacityWord,
    by simpa [hc] using h.chartCapacityReg,h.chartLengths,h.chartTarget,
    h.sitesFit,h.sitesWord,h.sites,h.siteCapacityWord,by simpa [hd] using h.siteCapacityReg,
    h.siteLengths,h.siteTarget⟩

structure SharedScanInput {m n : ℕ} (M W capacity : ℕ) (src : Fin m → Fin 3 → Fin n) (s : Env) : Prop where
  recovery : RecoveryLayout M m n s
  incidence : IncidenceInput s src
  canonical : Canonical M (s.arrs constraintMatrix)
  limit : (s.arrs constraintMatrix).length < W
  rhs : (s.arrs crtRhsBank).length = m+n
  active : capacity ≤ (s.arrs activeSlotBank).length
  coordLength : (s.arrs coordinateBank).length < W
  coordWords : ∀ v ∈ s.arrs coordinateBank, v < W
  probeLimit : s.vars scalarProbeLimit = n*M

private theorem SharedScanInput.setVar {M W m n capacity : ℕ} {s : Env} {src : Fin m → Fin 3 → Fin n}
    (h : SharedScanInput M W capacity src s) (r : String) (k : ℕ)
    (hNames : r ∉ [rowsR,inputColsR,modR,baseRows,scalarProbeLimit]) :
    SharedScanInput M W capacity src (s.setVar r k) := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hNames
  rcases hNames with ⟨hr,hc,hm,hb,hp⟩
  refine ⟨⟨?_,?_,?_,?_,h.recovery.sourceLen,h.recovery.workLen,h.recovery.workCanon,
    h.recovery.coLen,h.recovery.tgLen,h.recovery.modLen,h.recovery.destLen⟩,
    h.incidence,h.canonical,h.limit,h.rhs,h.active,h.coordLength,h.coordWords,?_⟩
  · simpa [Ne.symm hr] using h.recovery.rows
  · simpa [Ne.symm hc] using h.recovery.cols
  · simpa [Ne.symm hm] using h.recovery.modWord
  · simpa [Ne.symm hb] using h.recovery.base
  · simpa [Ne.symm hp] using h.probeLimit

local macro "keepLayout" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP14CRTLoop
    `EvenTI.P14Recovery.RecoveryLayout.fromFrame))

private theorem SharedScanInput.afterPrepare {M W m n capacity : ℕ} {s t : Env} {src : Fin m → Fin 3 → Fin n}
    (h : SharedScanInput M W capacity src s) (f : Frame prepareSelectedScanMode s t) :
    SharedScanInput M W capacity src t := by
  have hW : Canonical M (t.arrs matrixR) := (f.arrs matrixR (by decide)).symm ▸ h.recovery.workCanon
  have restored : RecoveryLayout M m n t := keepLayout h.recovery f (by decide) (by decide) (by decide) (by decide) hW
  exact ⟨restored,h.incidence.congr_env (f.arrs _ (by decide)),
    (f.arrs constraintMatrix (by decide)).symm ▸ h.canonical,(f.len _).trans_lt h.limit,
    (f.len _).trans h.rhs,(f.len _).symm ▸ h.active,(f.len _).trans_lt h.coordLength,
    (f.arrs coordinateBank (by decide)).symm ▸ h.coordWords,(f.vars _ (by decide)).trans h.probeLimit⟩

/-- Run the fixed selector and all CRT probes on actual stored mode tables.
The only input contract is the physical contents and bounds of those tables
and CRT scratch banks. All modes share their recovery workspace. -/
theorem scanSelectedModes_run {M W m n modes c d : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (plan : Fin modes → ScanModeInput W n)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hNM : n*M < W) (hCount : s.vars scanModeCount = modes) (hModes : modes < W)
    (hTables : SelectorData plan c d s) (hShared : SharedScanInput M W c src s) :
    ∃ t, Run W (scanAcrossModes prepareSelectedScanMode) s t
      ((20*c+20*d+69+scanInstalledModeCost M m n c+14)*modes+8) ∧ Frame (scanAcrossModes prepareSelectedScanMode) s t ∧
      SelectorData plan c d t ∧ SharedScanInput M W c src t ∧ t.vars scanAllAnswer ≤ 1 ∧
      (t.vars scanAllAnswer = 1 ↔ ∀ i, (plan i).scalar (M:=M) src) := by
  let Ready (u : Env) := SelectorData plan c d u ∧ SharedScanInput M W c src u
  have hOne : 1 < W := by omega
  have hM : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hnM : n ≤ n*M := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hM
  have hnW : n < W := hnM.trans_lt hNM
  have index (u : Env) (k : ℕ) (h : Ready u) : Ready (u.setVar scanModeCursor k) :=
    ⟨h.1.setVar _ _ (by decide) (by decide),h.2.setVar _ _ (by decide)⟩
  have answer (u : Env) (k : ℕ) (h : Ready u) : Ready (u.setVar scanAllAnswer k) :=
    ⟨h.1.setVar _ _ (by decide) (by decide),h.2.setVar _ _ (by decide)⟩
  have after (i : Fin modes) (u v : Env) (h : Ready u) (f : Frame scanInstalledMode u v)
      (hI : (plan i).installed (M:=M) src v) : Ready v := by
    refine ⟨h.1.ofFrame f (by decide) (by decide) (by decide) (by decide) (by decide),?_⟩
    exact ⟨hI.1.recovery,hI.1.incidence,hI.1.canonical,hI.1.capacity,hI.1.rhs,
      (f.len _).symm ▸ h.2.active,hI.1.coordLength,hI.1.coordWords,hI.2⟩
  have prep (i : Fin modes) (u : Env) (h : Ready u) (hi : u.vars scanModeCursor=i.val) :
      ∃ v, Run W prepareSelectedScanMode u v (20*c+20*d+69) ∧ (plan i).installed (M:=M) src v ∧ Ready v := by
    obtain ⟨v,rv,f,hL,hC,hZ,hR,hChart,hSite⟩ :=
      prepareSelectedScanMode_run plan h.1 i hi hOne ((plan i).reference.isLt.trans hnW)
    have p := h.2.afterPrepare f
    have hFit : (plan i).L ≤ c := (h.1.chartLengths i) ▸ (plan i).fitChart
    exact ⟨v,rv,⟨⟨p.recovery,p.incidence,p.canonical,p.limit,p.rhs,hChart,hSite,
      hFit.trans p.active,hL,hC,hZ,hR,p.coordLength,p.coordWords⟩,p.probeLimit⟩,
      ⟨h.1.ofFrame f (by decide) (by decide) (by decide) (by decide) (by decide),p⟩⟩
  have hCost (i : Fin modes) : scanInstalledModeCost M m n (plan i).L ≤ scanInstalledModeCost M m n c := by
    have hFit : (plan i).L ≤ c := (hTables.chartLengths i) ▸ (plan i).fitChart
    unfold scanInstalledModeCost
    refine Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) _
    unfold EvenTI.P19Scalar.InstalledProbe.runInstalledChartProbeCost
    omega
  obtain ⟨t,r,f,hReady,hBit,hSpec⟩ := scanAcrossModes_run src plan prepareSelectedScanMode Ready
    hW hRows hLayoutSize hNM hModes hCount hCost ⟨hTables,hShared⟩ index answer after
    (by decide) (by decide) (by decide) prep
  exact ⟨t,r,f,hReady.1,hReady.2,hBit,hSpec⟩

#print axioms scanSelectedModes_run
end EvenTI.P21ScalarScan
