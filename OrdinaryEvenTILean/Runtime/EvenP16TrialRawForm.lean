import EvenP16TrialFormInit
import EvenP15TrialInputTail
import EvenP14CutRawClock

set_option autoImplicit false
set_option maxHeartbeats 2250000

namespace EvenTI.P16Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Compare
open EvenTI.P15Trial (fieldVectorStart fieldVectorLength appendInput paidRun_appendInput)
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dL dZ dT dU dI dO)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawSelectedForm (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j) <|
    .seq emitFormInit <|
      .seq (.read cutChoiceIndex) <|
        .seq (cutCandidateProgram D F) (emitHigherForm D F)

noncomputable abbrev cutKernelDimension {d n : ℕ} (T S : Tensor K (d+d) n) (j : Fin 4) : ℕ :=
  Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))

/-- A literal raw pair plus one cap-admitted coefficient identifier emits
the exact public form encoding at an arbitrary balanced cut order. -/
theorem rawSelectedForm_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K (d+d) n) (j : Fin 4)
    (hd : 2 ≤ d) (hn : 2 ≤ n)
    (v : Fin (Fintype.card K ^ cutKernelDimension T S j))
    (hCap : Fintype.card K ^ cutKernelDimension T S j ≤ n) :
    let c := cutKernelDimension T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^d
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord d n → K), Run B (rawSelectedForm D F j)
      (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w++[v.val]))
        τ (rawCutSetupBitCost F L j+(emitFormInitCost+(1+(cutCandidateCost F c m+emitHigherFormCost F d m)))) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=cutFormWords D (fun x => ∑ i, coefficients D c v i * xs i x) ∧ τ.inp=[] := by
  dsimp only
  let c := cutKernelDimension T S j
  let m := n^d
  let o := placedRankSource m
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let B := (cutWordPoly F).eval (bitSize (comparisonInput D T S))
  obtain ⟨ρ,r₀,hW,hCuts,hNull,hBudget,_,hBank,hIn,hOut,hBig,hChoice⟩ :=
    rawCutSetupProgram_run D F T S j hd hn
  have hρ := paidRun_appendInput [v.val] r₀
  let ρ' := appendInput ρ [v.val]
  have hρS : Slots F canonical qN.WS Sn B ρ' := slots_frame F hW.frame.slots
    rfl rfl (fun _ _ => rfl) rfl
  have hdM : d ≤ m := (Nat.lt_two_pow_self (n := d)).le.trans (Nat.pow_le_pow_left hn _)
  have hnM : n ≤ m := (cutInput_side_bounds D T S (by omega : 1 ≤ d) hn).1
  let b := (outputBase j).value m
  have hWork : o+m ≤ b := hW.frame.layout.output_before
  have hBasisFit : b+m*m ≤ z := hW.frame.layout.basis_before
  have hZ : z+4=Sn := rfl
  have hFit : o+m ≤ Sn :=
    hWork.trans (((Nat.le_add_right b (m*m)).trans hBasisFit).trans
      (hZ ▸ Nat.le_add_right z 4))
  have hWord : Sn+m+m+10 < B := hBig
  have hBank' : ρ'.arrs rawPairIO.array=(d+d)::n::(tensorWords D T++tensorWords D S) := by
    simpa [ρ',appendInput,comparisonInput,List.append_assoc] using hBank
  obtain ⟨μ,rI,hμ,hMode,hBase,hSrc,hLen,hKeep,hVInit,hArr,hInI,hOutI⟩ :=
    emitFormInit_run F (n::(tensorWords D T++tensorWords D S)) (by omega) (by omega)
      (by omega) (by omega)
      (((Nat.le_add_right o m).trans hFit).trans_lt hρS.slots_word)
      hBank' hρS hBudget hW.frame.form_start hW.frame.side
  let η := {μ.setVar cutChoiceIndex v.val with inp := []}
  have hRead : μ.inp=[v.val] := by rw [hInI]; simp [ρ',appendInput,hIn]
  have r₁ : Run B (.read cutChoiceIndex) μ η 1 := Run.read hRead
  have hS₀ := Slots.setVar F canonical hμ (by decide : cutChoiceIndex ∉ regNames canonical)
    (by decide : cutChoiceIndex ≠ qN.WS) v.val
  have hS₁ : Slots F canonical qN.WS Sn B η := slots_frame F hS₀
    rfl rfl (fun _ _ => rfl) rfl
  have hRegs (r : String) (hbad : r ≠ cutChoiceIndex) (hg : r ∉ emitFormTargets) :
      η.vars r=ρ.vars r := by
    have hh : η.vars r=μ.vars r := by simp [η,hbad]
    exact hh.trans ((hKeep r hg).trans (show ρ'.vars r=ρ.vars r from rfl))
  have hVal (s : ℕ) : val F canonical qN.WS η s=val F canonical qN.WS ρ s :=
    (val_setVar F canonical (by decide : cutChoiceIndex ≠ qN.WS) μ v.val s).trans (hVInit s)
  have hFrame : CutRecombineInput (B := B) (Sn := Sn) F η (augmentedMatrixBase.value m)
      ((outputBase j).value m) o c m z (z+2) (z+3) := by
    exact ⟨hS₁,hW.frame.layout,hW.frame.count_word,
      (hRegs _ (by decide) (by decide)).trans hW.frame.coeff_start,
      (hRegs _ (by decide) (by decide)).trans hW.frame.basis_start,
      (hRegs _ (by decide) (by decide)).trans hW.frame.form_start,
      (hRegs _ (by decide) (by decide)).trans hW.frame.side,
      (hRegs _ (by decide) (by decide)).trans hW.frame.count,
      (hRegs _ (by decide) (by decide)).trans hW.frame.zero,
      (hRegs _ (by decide) (by decide)).trans hW.frame.scratch₁,
      (hRegs _ (by decide) (by decide)).trans hW.frame.scratch₂,
      (hVal _).trans hW.frame.zero_value⟩
  have hBLarge := (Nat.le_mul_of_pos_right (m+Fintype.card K+1)
    (by omega : 0 < m+Fintype.card K+1)).trans_lt hChoice
  have hQ : Fintype.card K < B := by omega
  have hPow : Fintype.card K^c < B := hCap.trans_lt (hnM.trans_lt (by omega))
  have hCoeffBank : c ≤ (η.arrs coefficientBank).length := by
    change c ≤ (μ.arrs coefficientBank).length
    rw [hArr]
    exact hW.coefficient_bank
  obtain ⟨α,r₂,hSlots,hValues,_,_,_,hV,hI₂,hO₂⟩ :=
    cutCandidateProgram_run D F v hFrame hQ hPow hCoeffBank rfl
      ((hRegs _ (by decide) (by decide)).trans hW.coefficient_count)
      ((hRegs _ (by decide) (by decide)).trans hW.load_base)
      ((hRegs _ (by decide) (by decide)).trans hW.load_count)
  have hNew (r : String) (hr : r ∉ regNames canonical) (hl : ¬ loadChanges r)
      (h₁ : r ≠ coeffIndex) (h₂ : r ≠ coeffPower) (h₃ : r ≠ coeffNumber)
      (h₄ : r ≠ dI) (h₅ : r ≠ dO) (h₆ : r ≠ cutEntry)
      (h₇ : r ≠ cutChoiceIndex) : α.vars r=μ.vars r := by
    have hh := hV r hr hl h₁ h₂ h₃ h₄ h₅ h₆
    simpa [η,h₇] using hh
  have hMode' : α.vars emitFormModes=d :=
    (hNew _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hMode
  have hBase' : α.vars reverseDigitBase=n :=
    (hNew _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hBase
  have hSrc' : α.vars fieldVectorStart=o :=
    (hNew _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hSrc
  have hLen' : α.vars fieldVectorLength=m :=
    (hNew _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)).trans hLen
  have hP : F.p < B := by
    have h := Nat.le_mul_of_pos_right (F.p+1) (by omega : 0 < F.p+1)
    have he := hSlots.base.arithmetic_word
    rw [pow_two] at he
    omega
  have hBasis := (hCuts j).basis
  rw [hNull] at hBasis
  obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
  let form : Coord d n → K := fun x => ∑ i, coefficients D c v i * xs i x
  have hf (x : Coord d n) : val F canonical qN.WS α (o+(inputCoordOrder n d x).val)=form x := by
    rw [hValues (inputCoordOrder n d x)]
    unfold form
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun y => coefficients D c v i*y) ((hVal _).trans (hAt i x))
  obtain ⟨τ,r₃,ho,_,hi,_⟩ := emitHigherForm_run D F form (by omega)
    (by omega) (by omega) (by omega) hSlots hQ.le hP (by omega)
    hFit hSrc' hLen' hBase' hMode' hf
  have hr := hρ.seq (rI.seq (r₁.seq (r₂.seq r₃)))
  refine ⟨τ,xs,hr,hInd,hSpan,?_,hi.trans hI₂⟩
  simpa [hO₂,η,hOutI,ρ',appendInput,hOut,form] using ho

#print axioms rawSelectedForm_run
end EvenTI.P16Trial