import EvenP15ReciprocalLayout
import EvenP15ReciprocalProducts
import Mathproof.Meta.IMPAutoCore20261004
import Mathproof.Meta.Problem18PairBoundaryModeC2Calls20261004
import Mathproof.Meta.Problem18PairBoundaryOddProductsRun20261004

set_option autoImplicit false

namespace EvenTI.P16Execution

open EvenTI.P15Execution
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairBoundaryMatrixPower20261004
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)
open Mathproof.Problem18PairBoundaryModeC2Calls20261004 (valid_of_vars)
open Mathproof.Problem18PairBoundaryOddRun20261004 (slots_of_vars)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- Squaring is the existing matrix-power machine with a two-bit exponent. -/
def squareLiveMatrix : Com :=
  .seq configureInverse (.seq (.assign exponentReg (.lit 2)) program)

/-- Run the full square from one installed input and three layout words.
The proof handles every input matrix, including singular ones. -/
theorem squareLiveMatrix_run (F : FieldPresentation K)
    {n input start S B : ℕ} {s : Env} (hn : 0 < n) (hB : 4 < B)
    (hApart : input+n*n ≤ start) (hFit : start+4*(n*n)+3 ≤ S)
    (hV : ValidMemory F B s) (hS : Slots F canonical ws S B s)
    (hN : s.vars inverseSizeWord=n) (hIn : s.vars inverseInputWord=input)
    (hStart : s.vars inverseOutputWord=start) (hMB : s.vars canonical.modBase+F.e ≤ s.vars ws) :
    ∃ t, Run B squareLiveMatrix s t (47+(2+programCost F.e n 2)) ∧
      matrix F t (s.vars ws+start*F.e) n n=(matrix F s (s.vars ws+input*F.e) n n)^2 ∧
      matrix F t (s.vars ws+input*F.e) n n=matrix F s (s.vars ws+input*F.e) n n ∧
      ValidMemory F B t ∧ Slots F canonical ws S B t ∧ Frame squareLiveMatrix s t := by
  obtain ⟨u,ru,hReg,hVu,hSu,hArr,_,_⟩ := configureInverse_run F hn hB hApart hFit hV hS hN hIn hStart
  have fu := Frame.of_run ru
  let v := u.setVar exponentReg 2
  have r₂ : Run B (.assign exponentReg (.lit 2)) u v 2 := Run.assign (evalB_lit (by omega))
  have hRead (r : String) (hr : r ≠ exponentReg) : v.vars r = u.vars r := by simp [v,hr]
  have hWS : v.vars ws = s.vars ws := (hRead _ (by decide)).trans (fu.vars _ (by decide))
  have hMod : v.vars canonical.modBase = s.vars canonical.modBase :=
    (hRead _ (by decide)).trans (fu.vars _ (by decide))
  have hVv : ValidMemory F B v := valid_of_vars F hVu rfl
    (hRead _ (by decide)) (hRead _ (by decide)) (hRead _ (by decide))
  have hSv : Slots F canonical ws S B v := slots_of_vars F hSu rfl (fun r hr => hRead r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with h|h|h|h|h <;> subst r <;> decide))
  have hRv := hReg.transfer (fun r hr => hRead r (by
    simp only [layoutRegs,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with h|h|h|h|h|h|h|h|h <;> subst r <;> decide))
  have hExp : v.vars exponentReg = 2 := by simp [v]
  have hMat : matrix F v (s.vars ws+input*F.e) n n = matrix F s (s.vars ws+input*F.e) n n := by
    apply matrix_of_cells F
    intro k _
    change (u.arrs canonical.mem).getD _ _ = _
    rw [hArr]
  let L := inverseLayout n input start
  obtain ⟨t,rt,hOut,hKeep,hVt,hSt,_,_,_,_,_,_,_,_,_⟩ :=
    program_run F L v (inverseLayout_ok hn hApart hFit) hRv hVv hSv
      (by rwa [hWS,hMod]) (by rw [hExp]; omega)
  have hTime : Nat.size (v.vars exponentReg) = 2 := by rw [hExp]; decide
  rw [hTime] at rt
  have run : Run B squareLiveMatrix s t (47+(2+programCost F.e n 2)) := ru.seq (r₂.seq rt)
  simp only [L,inverseLayout,hWS,hExp,hMat] at hOut hKeep
  exact ⟨t,run,hOut,hKeep,hVt,hSt,Frame.of_run run⟩

#print axioms squareLiveMatrix_run
end EvenTI.P16Execution