import EvenP22ScalarScanOrdinaryMode
import EvenP22ScalarScanPaddedMode
import EvenP22ScalarScanPipeline

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 850000

namespace EvenTI.P21ScalarScan

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

def scanPaddingKind : String := "even.p22.scalar.select.padding_kind"

def selectModePreparation (widths mult : String) : Com :=
  .ite (.eq (.var scanPaddingKind) (.lit 0)) (ordinaryModeWithSites widths mult)
    (.ite (.eq (.var scanPaddingKind) (.lit 1)) (paddedModeWithSites widths mult false)
      (paddedModeWithSites widths mult true))

def ModePreparation (widths mult : String) (kind : ℕ) : Com :=
  if kind=0 then ordinaryModeWithSites widths mult
  else paddedModeWithSites widths mult (decide (kind≠1))

/-- The selector consumes the actual mode kind already installed by its
prefix. The two padded choices use the same native row-site producer. -/
theorem selectModePreparation_run {W n kind C : ℕ} {s v : Env}
    (widths mult : String) (p : ScanModeInput W n)
    (hW : 2 < W) (hkind : kind ≤ 2) (hTag : s.vars scanPaddingKind=kind)
    (r : Run W (ModePreparation widths mult kind) s v C) (out : ScanModeOutput p v) :
    Run W (selectModePreparation widths mult) s v (C+8) ∧
      Frame (selectModePreparation widths mult) s v ∧ ScanModeOutput p v := by
  have hk : kind < W := by omega
  have hOne : 1 < W := by omega
  let isOrd := Cond.eq (.var scanPaddingKind) (.lit 0)
  let isLeft := Cond.eq (.var scanPaddingKind) (.lit 1)
  let ordinary := ordinaryModeWithSites widths mult
  let left := paddedModeWithSites widths mult false
  let right := paddedModeWithSites widths mult true
  have testOrd : isOrd.evalB W s=some (kind==0) :=
    evalB_condEq (ev_var hTag hk) (evalB_lit (by omega : 0 < W))
  have testLeft : isLeft.evalB W s=some (kind==1) :=
    evalB_condEq (ev_var hTag hk) (evalB_lit hOne)
  have rr : Run W (selectModePreparation widths mult) s v (C+8) := by
    by_cases h0 : kind=0
    · have rOrd : Run W ordinary s v C := by simpa [ModePreparation,h0,ordinary] using r
      have yes : isOrd.evalB W s=some true := by simpa [h0,beq_iff_eq] using testOrd
      exact (Run.ite_true (d:=.ite isLeft left right) yes rOrd).mono (by change 4+C ≤ C+8; omega)
    · have no : isOrd.evalB W s=some false := by rw [testOrd,beq_eq_false_iff_ne.mpr h0]
      have rPad : Run W (.ite isLeft left right) s v (C+4) := by
        by_cases h1 : kind=1
        · have rLeft : Run W left s v C := by simpa [ModePreparation,h0,h1,left] using r
          have yes : isLeft.evalB W s=some true := by simpa [h1,beq_iff_eq] using testLeft
          exact (Run.ite_true (d:=right) yes rLeft).mono (by change 4+C ≤ C+4; omega)
        · have rRight : Run W right s v C := by simpa [ModePreparation,h0,h1,right] using r
          have no : isLeft.evalB W s=some false := by rw [testLeft,beq_eq_false_iff_ne.mpr h1]
          exact (Run.ite_false (c:=left) no rRight).mono (by change 4+C ≤ C+4; omega)
      exact (Run.ite_false (c:=ordinary) no rPad).mono (by change 4+(C+4) ≤ C+8; omega)
  exact ⟨rr,Frame.of_run rr,out⟩

#print axioms selectModePreparation_run
end EvenTI.P21ScalarScan
