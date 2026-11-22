import EvenP21ScalarScanPublishLoop
import EvenP21ScalarScanSelected

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1600000

namespace EvenTI.P21ScalarScan

open scoped Matrix
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (arrayWrites scalarWrites)
open Mathproof.Problem18PairLargeFinalLoop20261004 (forLoop incr)

def publishThenScanModes (produce : Com) : Com :=
  .seq (publishAllScanModes produce) (scanAcrossModes prepareSelectedScanMode)

/-- Produce the records using the paid mode builder and consume the same
records in the exact homogeneous scan. The clock charges both outer loops. -/
theorem publishThenScanModes_run {M W m n modes c d T : ℕ} [NeZero M] {s : Env}
    (src : Fin m → Fin 3 → Fin n) (plan : Fin modes → ScanModeInput W n)
    (produce : Com) (Ready : Env → Prop)
    (hW : 4*M*M+4*M+10 < W) (hRows : 3*m < W)
    (hLayoutSize : (m+n+1)+n+(m+n+1)*n+(m+n+1)*(m+n+1)+4 < W)
    (hNM : n*M < W) (hCount : s.vars scanModeCount=modes) (hModes : modes < W)
    (hLayout : SelectorTableLayout plan c d s) (hReady : Ready s)
    (hCursorReady : ∀ u k, Ready u → Ready (u.setVar scanModeCursor k))
    (hAfter : ∀ u v, Ready u → Frame publishScanMode u v → Ready v)
    (hProdCur : scanModeCursor ∉ scalarWrites produce) (hProdCount : scanModeCount ∉ scalarWrites produce)
    (hProdC : selectorChartCapacity ∉ scalarWrites produce) (hProdD : selectorSitesCapacity ∉ scalarWrites produce)
    (hArchiveH : selectorHeaderBank ∉ arrayWrites produce)
    (hArchiveC : selectorChartTable ∉ arrayWrites produce)
    (hArchiveS : selectorSitesTable ∉ arrayWrites produce)
    (hProduce : ∀ (i : Fin modes) (u : Env), Ready u → u.vars scanModeCursor=i.val →
      ∃ v, Run W produce u v T ∧ ScanModeOutput (plan i) v ∧ Ready v)
    (hShared : ∀ u, Ready u → SharedScanInput M W c src u) :
    ∃ t, Run W (publishThenScanModes produce) s t
      (((T+20*c+20*d+72)*modes+6)+((20*c+20*d+69+scanInstalledModeCost M m n c+14)*modes+8)) ∧
      Frame (publishThenScanModes produce) s t ∧ SelectorData plan c d t ∧
      SharedScanInput M W c src t ∧ t.vars scanAllAnswer ≤ 1 ∧
      (t.vars scanAllAnswer=1 ↔ ∀ i, (plan i).scalar (M:=M) src) := by
  have hFour : 4 < W := by omega
  have hM : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hnM : n ≤ n*M := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n hM
  have hnW := hnM.trans_lt hNM
  obtain ⟨u,ru,fu,hData,hRU⟩ := publishAllScanModes_run plan produce Ready hFour hnW hModes hCount
    hLayout hReady hCursorReady hAfter hProdCur hProdCount hProdC hProdD hArchiveH hArchiveC hArchiveS hProduce
  have hKeep : scanModeCount ∉ scalarWrites (publishAllScanModes produce) := by
    have hd : scanModeCount ≠ scanModeCursor := by decide
    have hp : scanModeCount ∉ scalarWrites publishScanMode := by decide
    simp [publishAllScanModes,forLoop,incr,scalarWrites,hd,hProdCount,hp]
  obtain ⟨t,rt,_,hTables,hComm,hBit,hSpec⟩ := scanSelectedModes_run src plan hW hRows hLayoutSize hNM
    ((fu.vars _ hKeep).trans hCount) hModes hData (hShared _ hRU)
  have rr : Run W (publishThenScanModes produce) s t _ := ru.seq rt
  exact ⟨t,rr,Frame.of_run rr,hTables,hComm,hBit,hSpec⟩

#print axioms publishThenScanModes_run
end EvenTI.P21ScalarScan
