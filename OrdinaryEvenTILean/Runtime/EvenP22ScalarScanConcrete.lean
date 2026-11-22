import EvenP22ScalarScanInstalledCases
import EvenP22ScalarScanFrame

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1550000

namespace EvenTI.P21ScalarScan

open scoped Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)

local macro "setShared" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore `EvenP21ScalarScanSelected
    `EvenTI.P21ScalarScan.SharedScanInput.setVar))

private theorem modeScalars (widths mult : String) :
    scalarWrites (selectModePreparation widths mult)=scalarWrites (selectModePreparation "" "") := rfl
private theorem modeArrays (widths mult : String) :
    arrayWrites (selectModePreparation widths mult)=arrayWrites (selectModePreparation "" "") := rfl

private theorem selectModeKeepsShared (widths mult : String) :
    KeepsSharedScan (selectModePreparation widths mult) := by
  constructor <;> first | (rw [modeScalars]; decide) | (rw [modeArrays]; decide)

def buildPublishScan (load : Com) (widths mult : String) : Com :=
  publishThenScanModes (.seq load (selectModePreparation widths mult))

/-- Given the charged selected archive initializer, run the fixed mode
preparer, publication loop and homogeneous scan through one program. Its
source certificate describes live input banks, not a mode-answer callback. -/
theorem buildPublishScan_run
    {M W m n modes c d loadCost modeCost : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (plan : Fin modes → ScanModeInput W n)
    (load : Com) (widths mult : String) (Ready : Env → Prop)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hNM : n*M < W) (hCount : s.vars scanModeCount=modes) (hModes : modes < W)
    (hLayout : SelectorTableLayout plan c d s) (hReady : Ready s)
    (hShared : SharedScanInput M W c src s) (hLoadShared : KeepsSharedScan load)
    (hCursorReady : ∀ u k, Ready u → Ready (u.setVar scanModeCursor k))
    (hAfterPublish : ∀ u v, Ready u → Frame publishScanMode u v → Ready v)
    (hAfterMode : ∀ u v, Ready u → Frame (selectModePreparation widths mult) u v → Ready v)
    (hLoadCur : scanModeCursor ∉ scalarWrites load) (hLoadCount : scanModeCount ∉ scalarWrites load)
    (hLoadCapC : selectorChartCapacity ∉ scalarWrites load) (hLoadCapD : selectorSitesCapacity ∉ scalarWrites load)
    (hLoadHeader : selectorHeaderBank ∉ arrayWrites load)
    (hLoadChart : selectorChartTable ∉ arrayWrites load)
    (hLoadSites : selectorSitesTable ∉ arrayWrites load)
    (hLoad : ∀ (i : Fin modes) (u : Env), Ready u → u.vars scanModeCursor=i.val →
      ∃ v, Run W load u v loadCost ∧ Ready v ∧
        InstalledModePreparation widths mult (plan i) c modeCost v) :
    ∃ t, Run W (buildPublishScan load widths mult) s t
      (((loadCost+(modeCost+8)+20*c+20*d+72)*modes+6)+
        ((20*c+20*d+69+scanInstalledModeCost M m n c+14)*modes+8)) ∧
      Frame (buildPublishScan load widths mult) s t ∧ SelectorData plan c d t ∧
      SharedScanInput M W c src t ∧ t.vars scanAllAnswer ≤ 1 ∧
      (t.vars scanAllAnswer=1 ↔ ∀ i, (plan i).scalar (M:=M) src) := by
  let both (u : Env) := Ready u ∧ SharedScanInput M W c src u
  let produce := Com.seq load (selectModePreparation widths mult)
  have nextIdx (u : Env) (k : ℕ) (h : both u) : both (u.setVar scanModeCursor k) :=
    ⟨hCursorReady _ _ h.1,setShared h.2 scanModeCursor k (by decide)⟩
  have nextTable (u v : Env) (h : both u) (f : Frame publishScanMode u v) : both v :=
    ⟨hAfterPublish _ _ h.1 f,h.2.afterPublish f⟩
  have varKeep (r : String) (hL : r ∉ scalarWrites load)
      (hR : r ∉ scalarWrites (selectModePreparation "" "")) : r ∉ scalarWrites produce := by
    simpa only [produce,scalarWrites,Finset.mem_union,not_or,modeScalars] using And.intro hL hR
  have arrayKeep (r : String) (hL : r ∉ arrayWrites load)
      (hR : r ∉ arrayWrites (selectModePreparation "" "")) : r ∉ arrayWrites produce := by
    simpa only [produce,arrayWrites,Finset.mem_union,not_or,modeArrays] using And.intro hL hR
  have executed (i : Fin modes) (u : Env) (h : both u) (hi : u.vars scanModeCursor=i.val) :
      ∃ t, Run W produce u t (loadCost+(modeCost+8)) ∧ ScanModeOutput (plan i) t ∧ both t := by
    obtain ⟨v,r0,ready,prep⟩ := hLoad i u h.1 hi
    have sh := h.2.ofFrame (Frame.of_run r0) hLoadShared
    obtain ⟨t,r1,f1,hOut⟩ := installedModePreparation_run widths mult (plan i) prep
    exact ⟨t,r0.seq r1,hOut,hAfterMode _ _ ready f1,sh.ofFrame f1 (selectModeKeepsShared widths mult)⟩
  exact publishThenScanModes_run src plan produce both hW hRows hLayoutSize hNM hCount hModes
    hLayout ⟨hReady,hShared⟩ nextIdx nextTable (varKeep _ hLoadCur (by decide))
    (varKeep _ hLoadCount (by decide)) (varKeep _ hLoadCapC (by decide)) (varKeep _ hLoadCapD (by decide))
    (arrayKeep _ hLoadHeader (by decide)) (arrayKeep _ hLoadChart (by decide)) (arrayKeep _ hLoadSites (by decide))
    executed (fun _ h => h.2)

#print axioms buildPublishScan_run
end EvenTI.P21ScalarScan
