import EvenP15ReciprocalLayout
import EvenP15ReciprocalInverse

set_option autoImplicit false

namespace EvenTI.P15Execution

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18PairBoundaryMatrixPower20261004
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18P34AssemblyMatrixGramSetup20261003 (ws)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots)
open Mathproof.Problem18IMPFieldPrimitives20261001 (ValidMemory)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPMatrixMemory20261001 (matrix)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def invertLiveMatrix (q : ℕ) : Com := .seq configureInverse (loadedInverseProgram q)

/-- An inverse call from three caller registers and one installed matrix.
The call computes its layout and word exponent and leaves the input intact. -/
theorem invertLiveMatrix_run (F : FieldPresentation K)
    {n input start S B : ℕ} {s : Env} (hn : 0 < n) (hB : 4 < B)
    (hApart : input+n*n ≤ start) (hFit : start+4*(n*n)+3 ≤ S)
    (hV : ValidMemory F B s) (hS : Slots F canonical ws S B s)
    (hN : s.vars inverseSizeWord=n) (hIn : s.vars inverseInputWord=input)
    (hStart : s.vars inverseOutputWord=start) (hMB : s.vars canonical.modBase+F.e ≤ s.vars ws)
    (hWord : Fintype.card K^(n*n+n+2)<B)
    (hUnit : IsUnit (matrix F s (s.vars ws+input*F.e) n n)) :
    ∃ t, Run B (invertLiveMatrix (Fintype.card K)) s t (47+loadedInverseCost (Fintype.card K) F.e n) ∧
      matrix F t (s.vars ws+start*F.e) n n=(matrix F s (s.vars ws+input*F.e) n n)⁻¹ ∧
      matrix F t (s.vars ws+input*F.e) n n=matrix F s (s.vars ws+input*F.e) n n ∧
      ValidMemory F B t ∧ Slots F canonical ws S B t ∧ Frame (invertLiveMatrix (Fintype.card K)) s t := by
  obtain ⟨u,ru,hReg,hVu,hSu,hArr,_,_⟩ := configureInverse_run F hn hB hApart hFit hV hS hN hIn hStart
  have fu := Frame.of_run ru
  have hWS : u.vars ws = s.vars ws := fu.vars _ (by decide)
  have hMod : u.vars canonical.modBase = s.vars canonical.modBase := fu.vars _ (by decide)
  have hMU : matrix F u (u.vars ws+input*F.e) n n = matrix F s (s.vars ws+input*F.e) n n := by
    rw [hWS]
    apply matrix_of_cells F
    intro k _
    rw [hArr]
  have hnB : n < B := (Nat.le_mul_of_pos_right n hn).trans_lt
    (show n*n < B from by have h := hS.slots_word; omega)
  let L := inverseLayout n input start
  obtain ⟨t,rt,hInv,hKeep,hVt,hSt,_⟩ := loadedInverseProgram_run F L (inverseLayout_ok hn hApart hFit)
    hReg hVu hSu (by rwa [hWS,hMod]) hnB hWord (by change IsUnit (matrix F u (u.vars ws+input*F.e) n n); rwa [hMU])
  have run : Run B (invertLiveMatrix (Fintype.card K)) s t (47+loadedInverseCost (Fintype.card K) F.e n) := ru.seq rt
  simp only [L,inverseLayout,hWS] at hInv hKeep
  rw [hWS] at hMU
  rw [hMU] at hInv
  exact ⟨t,run,hInv,hKeep.trans hMU,hVt,hSt,Frame.of_run run⟩

#print axioms invertLiveMatrix_run
end EvenTI.P15Execution