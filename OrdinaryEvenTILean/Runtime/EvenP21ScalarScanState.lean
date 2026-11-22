import EvenP21ScalarScanVisit
import EvenP17ScalarProbeLoop

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 3500000

namespace EvenTI.P21ScalarScan

open EvenTI.P12Compare EvenTI.P14Recovery EvenTI.P15Recover EvenTI.P15Scalar
open EvenTI.P17Scalar (activeSlotBank activeWordAnswer scalarProbeCursor scalarProbeLimit)
open EvenTI.P18Scalar (arrayWords_of_run)
open EvenTI.P19Scalar.PrefixStencil
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15GSSSmithSweep20261007 (Canonical)
open Mathproof.P15GSSSmithSetup20261007 (rowsR)
open Mathproof.P15GSSSmithBanks20261007 (inputColsR)
open Mathproof.P15GSSSmithCoefficients20261007 (modR)
open Mathproof.P15GSSSmithMix20261007 (matrixR)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)

/-- The installed input and reusable scratch banks for one mode's CRT scan. -/
structure ScanInput {m n : ℕ} (M W L columns zero : ℕ)
    (src : Fin m → Fin 3 → Fin n) (chart sites : List ℕ) (reference : Fin n) (s : Env) : Prop where
  recovery : RecoveryLayout M m n s
  incidence : IncidenceInput s src
  canonical : Canonical M (s.arrs constraintMatrix)
  capacity : (s.arrs constraintMatrix).length < W
  rhs : (s.arrs crtRhsBank).length = m+n
  chartEq : s.arrs stencilChartBank = chart
  sitesEq : s.arrs stencilSitesBank = sites
  target : L ≤ (s.arrs activeSlotBank).length
  limit : s.vars stencilLimit = L
  cols : s.vars stencilColumns = columns
  zeroWord : s.vars stencilZero = zero
  referenceWord : s.vars stencilReference = reference.val
  coordLength : (s.arrs coordinateBank).length < W
  coordWords : ∀ v ∈ s.arrs coordinateBank, v < W

variable {M W m n L columns zero : ℕ} {src : Fin m → Fin 3 → Fin n}
  {chart sites : List ℕ} {reference : Fin n} {s t : Env}

theorem ScanInput.setVar (h : ScanInput M W L columns zero src chart sites reference s)
    (r : String) (v : ℕ)
    (hr : r ∉ [rowsR,inputColsR,modR,baseRows,
      stencilLimit,stencilColumns,stencilZero,stencilReference]) :
    ScanInput M W L columns zero src chart sites reference (s.setVar r v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  rcases hr with ⟨h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩
  refine ⟨?_,h.incidence,h.canonical,h.capacity,h.rhs,h.chartEq,h.sitesEq,h.target,
    ?_,?_,?_,?_,h.coordLength,h.coordWords⟩
  · refine ⟨?_,?_,?_,?_,h.recovery.sourceLen,h.recovery.workLen,h.recovery.workCanon,
      h.recovery.coLen,h.recovery.tgLen,h.recovery.modLen,h.recovery.destLen⟩
    · simpa [Ne.symm h₁] using h.recovery.rows
    · simpa [Ne.symm h₂] using h.recovery.cols
    · simpa [Ne.symm h₃] using h.recovery.modWord
    · simpa [Ne.symm h₄] using h.recovery.base
  · simpa [Ne.symm h₅] using h.limit
  · simpa [Ne.symm h₆] using h.cols
  · simpa [Ne.symm h₇] using h.zeroWord
  · simpa [Ne.symm h₈] using h.referenceWord

open EvenTI.P19Scalar.InstalledProbe (runInstalledChartProbe runInstalledChartProbeCost)

theorem ScanInput.afterProbe (h : ScanInput M W L columns zero src chart sites reference s)
    (r : Run W runInstalledChartProbe s t (runInstalledChartProbeCost M m n L))
    (f : Frame runInstalledChartProbe s t)
    (hRecover : RecoveryLayout M m n t) (hCanon : Canonical M (t.arrs constraintMatrix)) :
    ScanInput M W L columns zero src chart sites reference t := by
  exact ⟨hRecover,h.incidence.congr_env (f.arrs _ (by decide)),hCanon,
    (f.len _).trans_lt h.capacity,(f.len _).trans h.rhs,
    (f.arrs _ (by decide)).trans h.chartEq,(f.arrs _ (by decide)).trans h.sitesEq,
    (f.len _).symm ▸ h.target,(f.vars _ (by decide)).trans h.limit,
    (f.vars _ (by decide)).trans h.cols,(f.vars _ (by decide)).trans h.zeroWord,
    (f.vars _ (by decide)).trans h.referenceWord,(f.len _).trans_lt h.coordLength,
    arrayWords_of_run r coordinateBank h.coordWords⟩

def scanAnswer : String := "even.p21.scalar.scan.answer"

def andProbeAnswer : Com :=
  .ite (.eq (.var activeWordAnswer) (.lit 1)) .skip (.assign scanAnswer (.lit 0))

/-- Monotone conjunction of exact boolean probe verdicts in the live scan. -/
theorem andProbeAnswer_run {s : Env} {W : ℕ} (hW : 1 < W)
    (hBit : s.vars activeWordAnswer ≤ 1) :
    let t := if s.vars activeWordAnswer = 1 then s else s.setVar scanAnswer 0
    Run W andProbeAnswer s t 6 ∧
      t.vars scanAnswer ≤ s.vars scanAnswer ∧
      (t.vars scanAnswer = 1 ↔ s.vars scanAnswer = 1 ∧ s.vars activeWordAnswer = 1) := by
  let test : Cond := .eq (.var activeWordAnswer) (.lit 1)
  by_cases hy : s.vars activeWordAnswer = 1
  · have e : test.evalB W s = some true := evalB_condEq (ev_var hy hW) (evalB_lit hW)
    have rr : Run W andProbeAnswer s s 6 :=
      (Run.ite_true (d:=.assign scanAnswer (.lit 0)) e Run.skip).mono (by decide)
    simp [hy,rr]
  · have hz : s.vars activeWordAnswer = 0 := by omega
    have e : test.evalB W s = some false :=
      evalB_condEq (ev_var hz (by omega)) (evalB_lit (n:=1) hW)
    have rr : Run W andProbeAnswer s (s.setVar scanAnswer 0) 6 :=
      (Run.ite_false (c:=.skip) e (Run.assign (evalB_lit (by omega)))).mono (by decide)
    simp [hy,rr]

#print axioms ScanInput.afterProbe
#print axioms andProbeAnswer_run
end EvenTI.P21ScalarScan
