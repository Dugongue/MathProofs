import EvenP14CutRawSetup
import EvenP14CutRankInit

set_option autoImplicit false
set_option maxHeartbeats 1850000

namespace EvenTI.P12ComparePrep

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.LiveSpectral
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawRankedCutProgram (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j) (.seq (cutRankInit D F) (cappedRankedCutScan D F j))

theorem cutRankCodeGood_congr_bank (D : FieldEncoding K) (F : FieldPresentation K)
    {d n c : ℕ} {σ τ : Env} (j : Fin 4) (hc : c≤n^(d+1))
    (h : ∀ s < constantsBase.value (n^(d+1)), firstOutputBase.value (n^(d+1)) ≤ s →
      val F canonical qN.WS τ s = val F canonical qN.WS σ s) :
    cutRankCodeGood D F d n c σ j = cutRankCodeGood D F d n c τ j := by
  let m := n^(d+1)
  let b := (outputBase j).value m
  have hb : firstOutputBase.value m≤b := by rw [show b=_ from outputBase_value m j]; omega
  have htop : b+m*m≤constantsBase.value m := outputBank_point_upper m j
  funext v
  unfold cutRankCodeGood
  split
  · rename_i hv
    have hf : cutIndexedForm D F (d := d) (n := n) σ j ⟨v,hv⟩ =
        cutIndexedForm D F (d := d) (n := n) τ j ⟨v,hv⟩ := by
      funext x
      apply Finset.sum_congr rfl
      intro i _
      have hk : i.val*m+(inputCoordOrder n (d+1) x).val < m*m :=
        outputPoint_lt hc i (inputCoordOrder n (d+1) x)
      have hz := (Nat.add_lt_add_left hk b).trans_le htop
      have hlo := hb.trans (Nat.le_add_right b (i.val*m+(inputCoordOrder n (d+1) x).val))
      exact congrArg (fun x => coefficients D c ⟨v,hv⟩ i*x) (h _ hz hlo).symm
    exact congrArg rawRetainedFullRank hf
  · rfl

/-- A retained-rank cut scan from the literal original pair tape. The
accepted code predicate addresses the preserved basis in the final bank. -/
theorem rawRankedCutProgram_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (hd : 1≤d) (hn : 2≤n) :
    let w := comparisonInput D T S
    let L := bitSize w
    let B := (cutWordPoly F).eval L
    let m := n^(d+1)
    let Sn := pairCutSlotCount.value m
    let z := constantsBase.value m
    let c := Module.finrank K (selectedKernel (leftOf j) (if targetOf j then S else T))
    let q := Fintype.card K
    let count := cappedCutChoiceCount q c n
    let visit := cutCandidateCost F c m + ((cutRankModeCost F m+24)*(d+1)+14+10)
    let C := rawCutSetupBitCost F L j + (cutRankInitCost F+(30*(m+q)+42+((visit+8)*count+6)))
    ∃ τ, Run B (rawRankedCutProgram D F j) (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L))
        (w.length::w)) τ C ∧
      CutVisitInput (B := B) (Sn := Sn) F τ (augmentedMatrixBase.value m)
        ((outputBase j).value m) (placedRankSource m) c m z (z+2) (z+3) ∧
      (∃ xs : Fin c → Coord (d+1) n → K, LinearIndependent K xs ∧
        Submodule.span K (Set.range xs) = selectedKernel (leftOf j) (if targetOf j then S else T) ∧
        ∀ i x, val F canonical qN.WS τ ((outputBase j).value m+(i.val*m+(inputCoordOrder n (d+1) x).val))=xs i x) ∧
      τ.inp=[] ∧ τ.out=(List.range count).filter (cutRankCodeGood D F d n c τ j) := by
  dsimp only
  obtain ⟨ρ,hρ,hW,hCuts,hN,hBudget,hABI,hRaw,hIn,hOut,hBig,hChoice⟩ :=
    rawCutSetupProgram_run D F T S j (by omega : 2≤d+1) hn
  have hh : ρ.arrs rawPairIO.array=((d+1)+(d+1))::n::(tensorWords D T++tensorWords D S) := by
    simpa [comparisonInput,List.append_assoc] using hRaw
  have hQ : Fintype.card K ≤ (cutWordPoly F).eval (bitSize (comparisonInput D T S)) := by
    have hp : 0 < n^(d+1)+Fintype.card K+1 := by omega
    have hh' := (Nat.le_mul_of_pos_right (n^(d+1)+Fintype.card K+1) hp).trans_lt hChoice
    omega
  obtain ⟨α,hα,hWα,hReady,hNα,hBudgetα,hKeepα,hIα,hOα⟩ :=
    cutRankInit_run D F j _ hd hn hBig hQ hh hABI hN hBudget hW
  have hb := (cutInput_side_bounds D T S (by omega : 1≤d+1) hn).1
  obtain ⟨τ,hτ,hWτ,hKeep,hi,ho⟩ :=
    cappedRankedCutScan_run D F j hd hn hBig hChoice hNα hBudgetα hb hReady hWα
  refine ⟨τ,hρ.seq (hα.seq hτ),hWτ,?_,hi.trans (hIα.trans hIn),?_⟩
  · have hBasis := (hCuts j).basis
    rw [hN] at hBasis
    obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
    refine ⟨xs,hInd,hSpan,?_⟩
    intro i x
    let m := n^(d+1)
    let b := (outputBase j).value m
    let s := b+(i.val*m+(inputCoordOrder n (d+1) x).val)
    have hP : i.val*m+(inputCoordOrder n (d+1) x).val < m*m :=
      outputPoint_lt hW.frame.layout.nullity i (inputCoordOrder n (d+1) x)
    have hTop : b+m*m ≤ constantsBase.value m := outputBank_point_upper m j
    have hs : s<constantsBase.value m := (Nat.add_lt_add_left hP b).trans_le hTop
    have hlo : firstOutputBase.value m ≤ b := by rw [show b=_ from outputBase_value m j]; omega
    exact (hKeep s hs (hlo.trans (Nat.le_add_right _ _))).trans ((hKeepα s hs.le).trans (hAt i x))
  · rw [ho,hOα,hOut,List.nil_append,
      cutRankCodeGood_congr_bank D F j hW.frame.layout.nullity hKeep]

#print axioms rawRankedCutProgram_run
end EvenTI.P12ComparePrep
