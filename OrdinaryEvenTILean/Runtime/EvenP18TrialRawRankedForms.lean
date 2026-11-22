import EvenP18TrialRankForms
import EvenP18TrialRankMeaning
import EvenP14CutRawRankClock
import EvenP16TrialRawForm

set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option maxRecDepth 13000

namespace EvenTI.P18Trial

open EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep EvenTI.LiveSpectral
open EvenTI.P15Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax51.BinaryWordEncoding
open Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical arrayWrites)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem literalDispatch_arrayWrites (rows : List (ℕ × ℕ)) :
    arrayWrites (literalDispatch rows) = ∅ := by
  induction rows with
  | nil => rfl
  | cons p rows ih =>
    rcases p with ⟨k,v⟩
    simp [literalDispatch,arrayWrites,ih]

private theorem rankInit_keepsRaw (D : FieldEncoding K) (F : FieldPresentation K) :
    rawPairIO.array ∉ arrayWrites (cutRankInit D F) := by
  simpa only [cutRankInit,cutRankMakeOne,installEncodedDigit,arrayWrites,
    literalDispatch_arrayWrites,Finset.empty_union] using
    (show rawPairIO.array ∉ arrayWrites Mathproof.P15GEDigitLoad20261007.prog ∪
      arrayWrites cutRankConfigure from by decide)

noncomputable def rawRankedForms (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) : Com :=
  .seq (rawCutSetupProgram D F j) (.seq (cutRankInit D F) (.seq emitFormInit (rankedFormScan D F j)))

noncomputable def rawRankedFormsCost (F : FieldPresentation K) (q c d m n L : ℕ) (j : Fin 4) : ℕ :=
  rawCutSetupBitCost F L j + (cutRankInitCost F + (emitFormInitCost +
    (30*(m+q)+42+(((rankReadyVisitCost F d m c+(5+emitHigherFormCost F (d+1) m))+8)*
      cappedCutChoiceCount q c n+6))))

noncomputable def rankedBasisForms {d n c : ℕ} (D : FieldEncoding K)
    (xs : Fin c → Coord (d+1) n → K) : List (Coord (d+1) n → K) :=
  (linearChoices D xs n).filter (fun x => decide (x≠0) && rawRetainedFullRank x)

/-- Run the complete original-input capped rank scan and serialize its
successful forms. A single checked basis determines both the decisions and
the literal order of all form words. -/
theorem rawRankedForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    let c := cutKernelDimension T S j
    let w := comparisonInput D T S
    let L := bitSize w
    let m := n^(d+1)
    let Sn := pairCutSlotCount.value m
    let B := (cutWordPoly F).eval L
    ∃ (τ : Env) (xs : Fin c → Coord (d+1) n → K),
      Run B (rawRankedForms D F j)
        (initEnv (comparisonInitExt F Sn w.length (cutChoiceExt L)) (w.length::w))
        τ (rawRankedFormsCost F (Fintype.card K) c d m n L j) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      (∀ i x, val F canonical qN.WS τ
        ((outputBase j).value m+(i.val*m+(inputCoordOrder n (d+1) x).val))=xs i x) ∧
      τ.inp=[] ∧ τ.out=(rankedBasisForms D xs).flatMap (cutFormWords D) := by
  dsimp only
  let c := cutKernelDimension T S j
  let m := n^(d+1)
  let a := augmentedMatrixBase.value m
  let b := (outputBase j).value m
  let o := placedRankSource m
  let z := constantsBase.value m
  let Sn := pairCutSlotCount.value m
  let B := (cutWordPoly F).eval (bitSize (comparisonInput D T S))
  obtain ⟨ρ,r₀,hW,hCuts,hN,hBudget,hABI,hRaw,hIn,hOut,hBig,hChoice⟩ :=
    rawCutSetupProgram_run D F T S j (by omega : 2 ≤ d+1) hn
  have hRaw' : ρ.arrs rawPairIO.array=((d+1)+(d+1))::n::(tensorWords D T++tensorWords D S) := by
    simpa [comparisonInput,List.append_assoc] using hRaw
  have hQ : Fintype.card K ≤ B := by
    have h := (Nat.le_mul_of_pos_right (m+Fintype.card K+1) (by omega : 0 < m + Fintype.card K + 1)).trans_lt hChoice
    omega
  obtain ⟨α,rA,hA,hRank,hNA,hBA,hMemA,hInA,hOutA⟩ :=
    cutRankInit_run D F j _ hd hn hBig hQ hRaw' hABI hN hBudget hW
  have hRawA : α.arrs rawPairIO.array=((d+1)+(d+1))::n::(tensorWords D T++tensorWords D S) :=
    ((Frame.of_run rA).arrs _ (rankInit_keepsRaw D F)).trans hRaw'
  have hdm : d+1 ≤ m := (Nat.lt_two_pow_self (n := d+1)).le.trans (Nat.pow_le_pow_left hn _)
  have hnm : n ≤ m := (cutInput_side_bounds D T S (by omega : 1 ≤ d+1) hn).1
  have hWork : o+m ≤ b := hA.frame.layout.output_before
  have hBasisFit : b+m*m ≤ z := hA.frame.layout.basis_before
  have hZ : z+4=Sn := rfl
  have hCutW : Sn+m+m+10 < B := hBig
  obtain ⟨μ,rI,hμ,hMode,hBase,hSrc,hLen,hKeep,hVInit,hArr,hI,hO⟩ :=
    emitFormInit_run F (n::(tensorWords D T++tensorWords D S)) (by omega) (by omega)
      (by omega) (by omega) (show o<B by omega)
      (show α.arrs rawPairIO.array=((d+1)+(d+1))::(n::(tensorWords D T++tensorWords D S)) from hRawA)
      hA.frame.slots hBA hA.frame.form_start hA.frame.side
  have hFrame : CutRecombineInput (B := B) (Sn := Sn) F μ a b o c m z (z+2) (z+3) := by
    exact ⟨hμ,hA.frame.layout,hA.frame.count_word,
      (hKeep _ (by decide)).trans hA.frame.coeff_start,
      (hKeep _ (by decide)).trans hA.frame.basis_start,
      (hKeep _ (by decide)).trans hA.frame.form_start,
      (hKeep _ (by decide)).trans hA.frame.side,
      (hKeep _ (by decide)).trans hA.frame.count,
      (hKeep _ (by decide)).trans hA.frame.zero,
      (hKeep _ (by decide)).trans hA.frame.scratch₁,
      (hKeep _ (by decide)).trans hA.frame.scratch₂,
      (hVInit _).trans hA.frame.zero_value⟩
  have hVisit : CutVisitInput (B := B) (Sn := Sn) F μ a b o c m z (z+2) (z+3) :=
    ⟨hFrame,by rw [hArr];exact hA.coefficient_bank,
      (hKeep _ (by decide)).trans hA.coefficient_count,
      (hKeep _ (by decide)).trans hA.load_base,(hKeep _ (by decide)).trans hA.load_count⟩
  have hTargets : ∀ r ∈ cutRankArgNames, r ∉ emitFormTargets := by decide
  have hRankμ : CutRankStable (d := d) (n := n) F μ := by
    refine ⟨?_,(hVInit _).trans hRank.one⟩
    intro p hp
    have hName : p.1 ∈ cutRankArgNames := by
      change p.1 ∈ (cutRankArgs d n o (placedRankRows m) (placedRankAugmented m)
        (placedRankOutput m) z F.e).map Prod.fst
      exact List.mem_map.mpr ⟨p,hp,rfl⟩
    exact (hKeep _ (hTargets _ hName)).trans (hRank.regs p hp)
  have hNullμ : μ.vars (nullityAt j) = c := (hKeep _ (by fin_cases j <;> decide)).trans hNA
  obtain ⟨τ,rS,_,_,_,hPres,hInS,hOutS⟩ :=
    rankedFormScan_run D F j hd hn hBig hChoice hNullμ ((hKeep _ (by decide)).trans hBA) hnm
      hRankμ ⟨hMode,hBase,hSrc,hLen⟩ hVisit
  have hBasis := (hCuts j).basis
  rw [hN] at hBasis
  obtain ⟨xs,hInd,hSpan,hAt⟩ := hBasis
  have hLow : firstOutputBase.value m ≤ b := by rw [show b=_ from outputBase_value m j]; omega
  have within (i : Fin c) (x : Coord (d+1) n) :
      let p := b+(i.val*m+(inputCoordOrder n (d+1) x).val)
      p<z ∧ firstOutputBase.value m ≤ p := by
    dsimp only
    have hi : i.val*m+(inputCoordOrder n (d+1) x).val < m*m :=
      outputPoint_lt hW.frame.layout.nullity i (inputCoordOrder n (d+1) x)
    exact ⟨(Nat.add_lt_add_left hi b).trans_le hBasisFit, hLow.trans (Nat.le_add_right _ _)⟩
  have hAtμ (i : Fin c) (x : Coord (d+1) n) :
      val F canonical qN.WS μ (b+(i.val*m+(inputCoordOrder n (d+1) x).val))=xs i x :=
    (hVInit _).trans ((hMemA _ (within i x).1.le).trans (hAt i x))
  refine ⟨τ,xs,r₀.seq (rA.seq (rI.seq rS)),hInd,hSpan,?_,((hInS.trans hI).trans hInA).trans hIn,?_⟩
  · intro i x
    exact (hPres _ (within i x).1 (within i x).2).trans (hAtμ i x)
  · have hb : cutBankBasis (inputCoordOrder n (d+1)) (val F canonical qN.WS μ) b=xs :=
      funext fun i => funext (hAtμ i)
    rw [hOutS,hO,hOutA,hOut,List.nil_append,rankedBlocks_eq_bankForms D F (by omega : 0<n)]
    unfold bankForms rankedBasisForms
    rw [hb]

#print axioms rawRankedForms_run
end EvenTI.P18Trial
