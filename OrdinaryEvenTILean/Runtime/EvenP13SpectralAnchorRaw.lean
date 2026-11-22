import EvenP13SpectralAnchorCore
import EvenP13SpectralAnchorIO

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace EvenTI.P13Spectral

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.P10Scan
open EvenTI.PrimaryAlignment
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPConcreteEliminationBounds20261001 (macroBudget)
open Mathproof.Problem18P34AssemblyMatrixGatherSetup20261003 (install)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15FactorIMP20261007 (Bank Snf)
open Mathproof.P15DH2Bank20261007 (rNin)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.Problem17CharpolyExec
open Mathproof.Problem17BudgetExec (dimReg valueReg budgetCost budgetCost_le cap)
open Mathproof.Problem17RepeatedBudget (repeatedBudget)
open Mathproof.EvenTI.Singular.Coverage (repeatedBudget_le_degree_sq)
open Mathproof.Problem17CharpolyStage (dim)
open Mathproof.Problem17RecognizerAllocation (width)
open Mathproof.Problem17RecognizerWorkspace (reserve wordLimit)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def loadedAnchorProgram (D : FieldEncoding K) (F : FieldPresentation K) (input : String) : Com :=
  .seq (loadedAnchorCompute D F input) (.write (.var valueReg))

noncomputable def loadedAnchorCost (F : FieldPresentation K) (t : ℕ) : ℕ :=
  loadedAnchorComputeCost F t+2

/-- Start from the literal anchor words in an external bank and clean canonical
field arrays. The actual program initializes the field, reads the live
dimension, loads the matrix, and emits its exact repeated-primary exponent. -/
theorem loadedAnchor_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B t : Nat} {σ : Env} (A : Matrix (Fin (t+1)) (Fin (t+1)) K) (input : String)
    (hInput : input ≠ canonical.mem)
    (hData : σ.arrs input = numberedAnchorWords D (numeric A))
    (hlayout : OneAnchorLayout (width (t+1)) B t)
    (hWidth : width (t+1) < B) (hField : Fintype.card K ≤ B)
    (hMemory : σ.arrs canonical.mem = List.replicate (F.e+1+Snf (width (t+1))*F.e) 0)
    (hScratch : (σ.arrs canonical.scratch).length = 16*(F.e+1))
    (hMemFit : F.e+1+Snf (width (t+1))*F.e < B) (hScratchFit : 16*(F.e+1) < B)
    (hSquare : (F.p+1)^2 < B) (hPower : (F.p+1)^(F.e+1) < B)
    (hOff : 1+(t+1)*(t+1) < B) :
    ∃ τ, Run B (loadedAnchorProgram D F input) σ τ (loadedAnchorCost F t) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out ++ [storedAnchorExponent D (numeric A)] := by
  obtain ⟨η,hRun,hValue,hIn,hOut⟩ := loadedAnchorCompute_run D F A input hInput hData hlayout
    hWidth hField hMemory hScratch hMemFit hScratchFit hSquare hPower hOff
  rw [storedAnchorExponent_eq] at hValue
  have hm : repeatedBudget A.charpoly < B := by
    have h := repeatedBudget_le_degree_sq A.charpoly_monic
    rw [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin,pow_two] at h
    have hn : t+1 ≤ width (t+1) := by have := hlayout.degree; omega
    have hmul : (t+1)*(2*(t+1)+4) ≤ cap (width (t+1)) := by
      unfold cap
      apply Nat.mul_le_mul hn
      omega
    have : cap (width (t+1)) ≤ cap (width (t+1))*width (t+1) := by
      simpa using Nat.mul_le_mul_left (cap (width (t+1))) (show 1 ≤ width (t+1) by omega)
    have hb := hlayout.budget
    omega
  let τ := {η with out := η.out ++ [repeatedBudget A.charpoly]}
  have r₃ : Run B (.write (.var valueReg)) η τ 2 := by
    have h := evalB_var (B := B) (σ := η) (x := valueReg) (by rwa [hValue])
    rw [hValue] at h
    exact Run.write h
  have code : Run B (loadedAnchorProgram D F input) σ τ (loadedAnchorCost F t) :=
    hRun.seq r₃
  have dispatch (rs : List (Nat × Nat)) :
      noRead (literalDispatch rs) ∧ (literalDispatch rs).NoWrite := by
    induction rs with
    | nil => simp [literalDispatch,noRead,Com.NoWrite]
    | cons p rs ih => rcases p with ⟨k,v⟩; simpa [literalDispatch,noRead,Com.NoWrite] using ih
  have cIn : noRead oneAnchorCode := oneAnchor_noRead
  have cOut : oneAnchorCode.NoWrite := oneAnchor_noWrite
  have iIn : noRead Mathproof.P15GEDigitLoad20261007.prog := by apply noRead_of_check; rfl
  have iOut : Mathproof.P15GEDigitLoad20261007.prog.NoWrite := by apply noWrite_of_check; rfl
  have bodyIn : noRead (oneAnchorFromLabels D F input) := by
    simpa [oneAnchorFromLabels,encodedBankLoad,encodedBankLoadStep,installEncodedDigit,noRead,cIn,iIn]
      using (dispatch (literalTable D F)).1
  have bodyOut : (oneAnchorFromLabels D F input).NoWrite := by
    simpa [oneAnchorFromLabels,encodedBankLoad,encodedBankLoadStep,installEncodedDigit,Com.NoWrite,cOut,iOut]
      using (dispatch (literalTable D F)).2
  refine ⟨τ,code,hIn bodyIn,?_⟩
  change η.out ++ [repeatedBudget A.charpoly] = σ.out ++ [storedAnchorExponent D (numeric A)]
  rw [hOut bodyOut,storedAnchorExponent_eq]

theorem loadedAnchorCost_le (F : FieldPresentation K) {t L : Nat} (hL : (t+1)*(t+1)+1 ≤ L) :
    let X := reserve (anchorInputScale F L)
    loadedAnchorCost F t ≤ (3*F.e+222+encodedBankLoadStepCost F contiguousAddress+
      configCost false+fromBankFactor+5000000)*X^7 := by
  let X := reserve (anchorInputScale F L)
  let c := 3*F.e+220+encodedBankLoadStepCost F contiguousAddress+
      configCost false+fromBankFactor+5000000
  have h : loadedAnchorComputeCost F t ≤ c*X^7 := loadedAnchorComputeCost_le F hL
  have hSmall : 1 ≤ L+F.e+macroBudget F+12 := by omega
  have hX : 1 ≤ X := by
    let y := L+F.e+macroBudget F+12
    change 1 ≤ 10000000*(y^2)^5
    have hy : 1 ≤ (y^2)^5 := Nat.one_le_pow 5 _ (Nat.one_le_pow 2 _ hSmall)
    exact hy.trans (by simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right ((y^2)^5) (by decide : 1 ≤ 10000000))
  have hg : 2 ≤ 2*X^7 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 (Nat.one_le_pow _ _ hX)
  have hc : c+2 = 3*F.e+222+encodedBankLoadStepCost F contiguousAddress+
      configCost false+fromBankFactor+5000000 := by dsimp [c]; omega
  calc
    loadedAnchorCost F t = loadedAnchorComputeCost F t+2 := rfl
    _ ≤ c*X^7+2*X^7 := Nat.add_le_add h hg
    _ = _ := by rw [← Nat.add_mul,hc]

#print axioms loadedAnchor_run
#print axioms loadedAnchorCost_le
end EvenTI.P13Spectral
