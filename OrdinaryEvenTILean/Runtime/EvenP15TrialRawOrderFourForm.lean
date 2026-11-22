import EvenP15TrialOrderFourForm
import EvenP15TrialInputTail

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P15Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)
open Mathproof.P15RecogIMPDot20261007 (qN dZ dT dU dI dO)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawOrderFourFormProgram (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j) <|
    .seq (.read cutChoiceIndex) <|
      .seq (cutCandidateProgram D F) (orderFourFormWriter D F)

noncomputable abbrev selectedFourNullity {n : ℕ} (T S : Tensor K (2+2) n) (j : Fin 4) : ℕ :=
  Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))

/-- The literal raw pair, followed by one admitted coefficient code, produces
the exact public form words for the selected cut. The coefficient form is
reconstructed from the physically installed native kernel basis. -/
theorem rawOrderFourFormProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {n : ℕ} (T S : Tensor K (2+2) n) (j : Fin 4) (hn : 2 ≤ n)
    (v : Fin (Fintype.card K ^ selectedFourNullity T S j))
    (hCap : Fintype.card K ^ selectedFourNullity T S j ≤ n) :
    let c := selectedFourNullity T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^2
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord 2 n → K), Run B (rawOrderFourFormProgram D F j)
      (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w++[v.val]))
        τ (rawCutSetupBitCost F L j+(1+(cutCandidateCost F c m+orderFourFormCost F m))) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=cutFormWords D (fun x => ∑ i, coefficients D c v i * xs i x) ∧ τ.inp=[] := by
  dsimp only
  let c := selectedFourNullity T S j
  let m := n^2
  let o := placedRankSource m
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let B := (cutWordPoly F).eval (bitSize (comparisonInput D T S))
  obtain ⟨ρ,r₀,hW,hCuts,hN,hBudget,hABI,hBank,hIn,hOut,hBig,hChoice⟩ :=
    rawCutSetupProgram_run D F T S j (by decide : 2 ≤ 2) hn
  have hρ := paidRun_appendInput [v.val] r₀
  let ρ' := appendInput ρ [v.val]
  let η := {ρ.setVar cutChoiceIndex v.val with inp := []}
  have hRead : ρ'.inp=[v.val] := by simp [ρ',appendInput,hIn]
  have r₁ : Run B (.read cutChoiceIndex) ρ' η 1 := Run.read hRead
  have hS₀ := Slots.setVar F canonical hW.frame.slots (by decide : cutChoiceIndex ∉ regNames canonical)
    (by decide : cutChoiceIndex ≠ qN.WS) v.val
  have hS₁ : Slots F canonical qN.WS Sn B η := slots_frame F hS₀ rfl rfl (fun _ _ => rfl) rfl
  have hFrame : CutRecombineInput (B := (cutWordPoly F).eval (bitSize (comparisonInput D T S))) (Sn := Sn) F η (augmentedMatrixBase.value m) ((outputBase j).value m)
      o c m z (z+2) (z+3) :=
    ⟨hS₁,hW.frame.layout,hW.frame.count_word,hW.frame.coeff_start,hW.frame.basis_start,
      hW.frame.form_start,hW.frame.side,hW.frame.count,hW.frame.zero,hW.frame.scratch₁,hW.frame.scratch₂,
      (val_setVar F canonical (by decide : cutChoiceIndex ≠ qN.WS) ρ v.val z).trans hW.frame.zero_value⟩
  have Blarge := (Nat.le_mul_of_pos_right (m+Fintype.card K+1)
    (by omega : 0 < m+Fintype.card K+1)).trans_lt hChoice
  have hQ : Fintype.card K < (cutWordPoly F).eval (bitSize (comparisonInput D T S)) := by omega
  have hnM : n ≤ m := (cutInput_side_bounds D T S (by decide : 1 ≤ 2) hn).1
  have hPow : Fintype.card K^c < (cutWordPoly F).eval (bitSize (comparisonInput D T S)) :=
    hCap.trans_lt (hnM.trans_lt (by omega))
  obtain ⟨α,r₂,hSlots,hValues,_,_,hMem,hV,hI₂,hO₂⟩ :=
    cutCandidateProgram_run D F v hFrame hQ hPow hW.coefficient_bank rfl
      hW.coefficient_count hW.load_base hW.load_count
  have hBase' : α.vars cutFormStart=o :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hFrame.form_start
  have hSide' : α.vars shapePower.out=m :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hFrame.side
  have hN' : α.vars cutChoiceBudget=n :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hBudget
  have hZ' : α.vars dZ=z :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hFrame.zero
  have hT' : α.vars dT=z+2 :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hFrame.scratch₁
  have hU' : α.vars dU=z+3 :=
    (hV _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      hFrame.scratch₂
  have hZSn : z+4=Sn := rfl
  have hB' : Sn+m+m+10 < B := hBig
  let b := (outputBase j).value m
  have hao : augmentedMatrixBase.value m+c ≤ o := hFrame.layout.coefficient_before
  have hbo : o+m ≤ b := hFrame.layout.output_before
  have hbz : b+m*m ≤ z := hFrame.layout.basis_before
  have hmp : 0 < m := pow_pos (by omega) _
  have hml : m ≤ m*m := Nat.le_mul_of_pos_right _ hmp
  have hKeepZero : val F canonical qN.WS α z=0 :=
    (hMem z (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega)).trans hFrame.zero_value
  have hP : F.p < B := by
    have h := Nat.le_mul_of_pos_right (F.p+1) (by omega : 0 < F.p+1)
    have he := hSlots.base.arithmetic_word
    rw [pow_two] at he
    omega
  have hBasis := (hCuts j).basis
  rw [hN] at hBasis
  obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
  let form : Coord 2 n → K := fun x => ∑ i, coefficients D c v i * xs i x
  have hf (x : Coord 2 n) : val F canonical qN.WS α (o+(inputCoordOrder n 2 x).val)=form x := by
    rw [hValues (inputCoordOrder n 2 x)]
    unfold form
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z => coefficients D c v i*z) (hAt i x)
  have mm : n*n=m := (pow_two n).symm
  obtain ⟨τ,r₃,ho,hi⟩ := orderFourFormWriter_run D F form hn
    (by rw [mm]; omega) hZSn.le (by omega) hQ.le hP hSlots hN'
    (by rw [mm]; exact hSide') hBase' hZ' hT' hU' hKeepZero hf (by rw [mm])
  have hr : Run B (rawOrderFourFormProgram D F j)
      (initEnv (comparisonInitExt F Sn (comparisonInput D T S).length (cutChoiceExt (bitSize (comparisonInput D T S))))
        ((comparisonInput D T S).length::(comparisonInput D T S)++[v.val])) τ
      (rawCutSetupBitCost F (bitSize (comparisonInput D T S)) j+
        (1+(cutCandidateCost F c m+orderFourFormCost F m))) := by
    rw [mm] at r₃
    exact hρ.seq (r₁.seq (r₂.seq r₃))
  exact ⟨τ,xs,hr,hInd,hSpan,by simpa [hO₂,η,hOut,form] using ho,by simpa [hI₂,η] using hi⟩

#print axioms rawOrderFourFormProgram_run
end EvenTI.P15Trial
