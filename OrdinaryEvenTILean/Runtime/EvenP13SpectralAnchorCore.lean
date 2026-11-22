import EvenP13SpectralAnchorLayout
import EvenP12ComparePrepField

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

noncomputable def loadedAnchorCompute (D : FieldEncoding K)
    (F : FieldPresentation K) (input : String) : Com :=
  .seq (fieldInitProgram F) (.seq (anchorRegisters input) (oneAnchorFromLabels D F input))

noncomputable def loadedAnchorComputeCost (F : FieldPresentation K) (t : ℕ) : ℕ :=
  (3*F.e+13)+(95+(encodedBankLoadCost F contiguousAddress ((t+1)*(t+1))+
    oneAnchorCost F t (width (t+1))))

/-- Start from the literal anchor words in an external bank and clean canonical
field arrays. The actual program initializes the field, reads the live
dimension, loads the matrix, and computes its exact repeated-primary exponent. -/
theorem loadedAnchorCompute_run (D : FieldEncoding K) (F : FieldPresentation K)
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
    ∃ τ, Run B (loadedAnchorCompute D F input) σ τ (loadedAnchorComputeCost F t) ∧
      τ.vars valueReg = storedAnchorExponent D (numeric A) ∧
      (noRead (oneAnchorFromLabels D F input) → τ.inp = σ.inp) ∧
      ((oneAnchorFromLabels D F input).NoWrite → τ.out = σ.out) := by
  let N := width (t+1)
  let μ := fieldInitState F σ
  obtain ⟨r₀,hSlots,hws,_,hArr,_,hInp,hOut⟩ :=
    fieldInitProgram_run F (Snf N) B σ hMemory hScratch hMemFit hScratchFit hSquare hPower
      (by change Snf (width (t+1)) < B; have := hlayout.word; omega)
  have hBase : μ.vars canonical.modBase = 0 := by
    change (install (fieldRegisterValues F) σ).vars canonical.modBase = 0
    simp [fieldRegisterValues,install,canonical,qN,
      Mathproof.Problem18ConcreteSolverNames20261002.names]
  have hd : (μ.arrs input)[0]? = some (t+1) := by
    rw [hArr input hInput,hData]
    rfl
  obtain ⟨ρ,r₁,hOrder,hLen,hN,hLoad,hOff',hR⟩ :=
    anchorRegisters_run input hd (by omega) hWidth
  have hKeep : ∀ x ∈ regNames canonical, x ∉ scalarWrites (anchorRegisters input) := by
    intro x hx
    have hf : ∀ y ∈ [dimReg,loadLength,rNin,loadBase,inputBase], y ∉ regNames canonical := by decide
    have hn (y : String) (hy : y ∈ [dimReg,loadLength,rNin,loadBase,inputBase]) :
        x ≠ y := fun e => hf y hy (e ▸ hx)
    simp [anchorRegisters,scalarWrites,hn dimReg (by simp),hn loadLength (by simp),
      hn rNin (by simp),hn loadBase (by simp),hn inputBase (by simp)]
  have hWS' : ρ.vars qN.WS = μ.vars qN.WS := hR.vars _ (by simp [anchorRegisters,scalarWrites,qN,inputBase,loadBase,loadLength,rNin,dimReg,canonical,Mathproof.Problem17ComparatorReader.rN,Mathproof.Problem18ConcreteSolverNames20261002.names])
  have hS := slots_frame F hSlots (hR.arrs _ (by simp [anchorRegisters,arrayWrites])) (hR.arrs _ (by simp [anchorRegisters,arrayWrites]))
    (fun x hx => hR.vars x (hKeep x hx)) hWS'
  have h0 : OneAnchorState F N B t ρ :=
    ⟨hS,hWS'.trans hws,(hR.vars _ (by simp [anchorRegisters,scalarWrites,qN,inputBase,loadBase,loadLength,rNin,dimReg,canonical,Mathproof.Problem17ComparatorReader.rN,Mathproof.Problem18ConcreteSolverNames20261002.names])).trans hBase,
      (hR.len _).trans (((Frame.of_run r₀).len _).trans (by rw [hMemory,List.length_replicate])),
      hN,hOrder⟩
  obtain ⟨η,r₂,hBank,hValue,hFrame⟩ := oneAnchorFromLabels_run D F A input hInput hlayout h0
    hField hOff hLoad hLen hOff' (fun j => by
      rw [hR.arrs _ (by simp [anchorRegisters,arrayWrites]),hArr input hInput,hData]
      have hi : j.val < (List.ofFn fun i : Fin ((t+1)*(t+1)) =>
          (D (A (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)).val).length := by
        simpa only [List.length_ofFn] using j.isLt
      simp only [numberedAnchorWords,numeric,Nat.add_comm 1,List.getElem?_cons_succ]
      rw [List.getElem?_eq_getElem hi,List.getElem_ofFn])
  refine ⟨η,r₀.seq (r₁.seq r₂),by simpa [storedAnchorExponent_eq,numeric] using hValue,?_,?_⟩
  · intro h
    exact (hFrame.inp h).trans ((hR.inp (by apply noRead_of_check; rfl)).trans hInp)
  · intro h
    exact (hFrame.out h).trans ((hR.out (by apply noWrite_of_check; rfl)).trans hOut)

theorem loadedAnchorComputeCost_le (F : FieldPresentation K) {t L : Nat} (hL : (t+1)*(t+1)+1 ≤ L) :
    let X := reserve (anchorInputScale F L)
    loadedAnchorComputeCost F t ≤
      (3*F.e+220+encodedBankLoadStepCost F contiguousAddress+configCost false+
        fromBankFactor+5000000)*X^7 := by
  let X := reserve (anchorInputScale F L)
  obtain ⟨_,_,_,_,hM,hD,hN,he,ht⟩ := anchorFits F hL
  change macroBudget F ≤ X at hM
  change _ ≤ X at hN
  have hX : 1 ≤ X := by omega
  have hp : X^6 ≤ X^7 := Nat.pow_le_pow_right hX (by decide)
  have hu : 1 ≤ X^7 := Nat.one_le_pow _ _ hX
  have hv : L ≤ X^7 := by
    let x := anchorInputScale F L
    have h₁ : L ≤ x := by
      unfold x anchorInputScale
      exact (show L ≤ L+F.e+macroBudget F+12 by omega).trans
        (Nat.le_self_pow (n := 2) (by decide) _)
    have h₂ : x ≤ X := by
      dsimp only [X]
      unfold reserve
      exact (Nat.le_self_pow (n := 5) (by decide) x).trans
        (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (x^5) (by decide : 1 ≤ 10000000))
    exact (h₁.trans h₂).trans (Nat.le_self_pow (n := 7) (by decide) X)
  have h₁ := (fromBank_cost_le F (t := t) hM hD ht (show width (t+1)+width (t+1) ≤ X by omega) he).trans
    (Nat.mul_le_mul_left _ hp)
  have h₂ := budgetCost_le F hX hM (show width (t+1)+1 ≤ X by omega)
  have h₃ := Nat.mul_le_mul_left (4+encodedBankLoadStepCost F contiguousAddress)
    (show (t+1)*(t+1) ≤ X^7 by omega)
  let A := 3*F.e+220+encodedBankLoadStepCost F contiguousAddress+configCost false
  have h₄ : 3*F.e+176+configCost false ≤ (3*F.e+216+configCost false)*X^7 := by
    exact (show 3*F.e+176+configCost false ≤ 3*F.e+216+configCost false by omega).trans
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left _ hu)
  change loadedAnchorComputeCost F t ≤ (A+fromBankFactor+5000000)*X^7
  let a := configCost false
  let k := encodedBankLoadStepCost F contiguousAddress
  let u := fromBankCost F t (width (t+1)+width (t+1))
  let v := budgetCost F (width (t+1))
  have bound := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h₄ h₃) h₁) h₂
  calc
    loadedAnchorComputeCost F t =
        3*F.e+174+a+(4+k)*((t+1)*(t+1))+u+v := by
      unfold loadedAnchorComputeCost oneAnchorCost encodedBankLoadCost
      change 3*F.e+13+(95+((k+4)*((t+1)*(t+1))+6+(a+(u+(60+v))))) = _
      ring
    _ ≤ 3*F.e+176+a+(4+k)*((t+1)*(t+1))+u+v := by omega
    _ ≤ (3*F.e+216+a)*X^7+(4+k)*X^7+fromBankFactor*X^7+5000000*X^7 := bound
    _ = (A+fromBankFactor+5000000)*X^7 := by
      change (3*F.e+216+a)*X^7+(4+k)*X^7+fromBankFactor*X^7+5000000*X^7 =
        (3*F.e+220+k+a+fromBankFactor+5000000)*X^7
      ring

#print axioms loadedAnchorCompute_run
#print axioms loadedAnchorComputeCost_le
end EvenTI.P13Spectral
