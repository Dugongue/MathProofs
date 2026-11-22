import EvenP18TrialRawRankedForms
import EvenP15Totalizer

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace EvenTI.P18Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax51.TuringPolytime
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawRankedFormsPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawRankedBitPoly F j+C emitFormInitCost+
    ((C 24*X+C (26+emitFieldLabelCost F))*X+C 6)*X

theorem rawRankedFormsCost_le (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    let L := bitSize (comparisonInput D T S)
    rawRankedFormsCost F (Fintype.card K) (cutKernelDimension T S j) d (n^(d+1)) n L j ≤
      (rawRankedFormsPoly F j).eval L := by
  dsimp only
  let c := cutKernelDimension T S j
  let m := n^(d+1)
  let q := Fintype.card K
  let L := bitSize (comparisonInput D T S)
  let N := cappedCutChoiceCount q c n
  let E := (24*L+(26+emitFieldLabelCost F))*L+6
  let A := rankReadyVisitCost F d m c+10+8
  obtain ⟨hnM,hmL,hdL⟩ := cutInput_side_bounds D T S (by omega : 1 ≤ d+1) hn
  have hnL := hnM.trans hmL
  have hcL : c ≤ L := (kernelFinrank_le _).trans hmL
  have hScan : 30*(m+q)+42+(A*N+6) ≤
      (cutRankedPaidPoly F q).eval L := by
    simpa only [A,rankReadyVisitCost,Nat.add_assoc] using rankedCutScanCost_le F hdL hcL hmL hnL
  have hEmit : emitHigherFormCost F (d+1) m ≤ E := by
    simp only [emitHigherFormCost,E,Nat.add_assoc]
    gcongr
  have hOnce : rankReadyVisitCost F d m c + (5+emitHigherFormCost F (d+1) m)+8 ≤ A+E := by
    dsimp [A]
    omega
  have hLoop := Nat.mul_le_mul_right N hOnce
  rw [Nat.add_mul A E N] at hLoop
  have hCount : N ≤ L := (cappedCutChoiceCount_le q c n).trans hnL
  have hTotal := Nat.mul_le_mul_left E hCount
  change rawRankedFormsCost F q c d m n L j ≤ (rawRankedFormsPoly F j).eval L
  simp only [rawRankedFormsCost,rawRankedFormsPoly,rawRankedBitPoly,eval_add,eval_C,
    eval_mul,eval_X,rawSetupBitPoly_eval]
  change rawCutSetupBitCost F L j+(cutRankInitCost F+(emitFormInitCost+
    (30*(m+q)+42+(((rankReadyVisitCost F d m c+(5+emitHigherFormCost F (d+1) m))+8)*N+6)))) ≤
    rawCutSetupBitCost F L j+(cutRankInitCost F+(cutRankedPaidPoly F q).eval L)+emitFormInitCost+E*L
  omega

private def rawRankedValid (D : FieldEncoding K) (w : List ℕ) : Prop :=
  ∃ (d n : ℕ) (T S : Tensor K ((d+1)+(d+1)) n), 1 ≤ d ∧ 2 ≤ n ∧ w=comparisonInput D T S

private noncomputable def rankedFormsExtension (F : FieldPresentation K) (w : List ℕ) : String → ℕ :=
  let d := (w.headD 0)/2
  let n := w[1]?.getD 0
  comparisonInitExt F (pairCutSlotCount.value (n^d)) w.length (cutChoiceExt (bitSize w))

private theorem rankedFormsExtension_eq (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K ((d+1)+(d+1)) n) :
    rankedFormsExtension F (comparisonInput D T S) =
      comparisonInitExt F (pairCutSlotCount.value (n^(d+1))) (comparisonInput D T S).length
        (cutChoiceExt (bitSize (comparisonInput D T S))) := by
  simp [rankedFormsExtension,comparisonInput,show (d+1+(d+1))/2=d+1 by omega]

private def rankedFormsRun (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (w : List ℕ) (τ : Env) : Prop :=
  Run ((cutWordPoly F).eval (bitSize w)) (rawRankedForms D F j)
    (initEnv (rankedFormsExtension F w) (w.length::w)) τ ((rawRankedFormsPoly F j).eval (bitSize w))

private noncomputable def rankedFormsReference (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (w : List ℕ) : List ℕ := by
  classical
  exact if h : ∃ τ, rankedFormsRun D F j w τ then h.choose.out else []

private theorem rankedFormsReference_eq {D : FieldEncoding K} {F : FieldPresentation K}
    {j : Fin 4} {w : List ℕ} {τ : Env} (h : rankedFormsRun D F j w τ) :
    rankedFormsReference D F j w=τ.out := by
  classical
  have hE : ∃ t, rankedFormsRun D F j w t := ⟨τ,h⟩
  unfold rankedFormsReference
  rw [dif_pos hE]
  obtain ⟨k,_,h₁⟩ := Run.bigStep (Classical.choose_spec hE)
  obtain ⟨l,_,h₂⟩ := Run.bigStep h
  exact congrArg Env.out (BigStep.unique h₁ h₂).1

private theorem rankedFormsRun_ready (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (hd : 1 ≤ d) (hn : 2 ≤ n) :
    let c := cutKernelDimension T S j
    ∃ (τ : Env) (xs : Fin c → Coord (d+1) n → K), rankedFormsRun D F j (comparisonInput D T S) τ ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=(rankedBasisForms D xs).flatMap (cutFormWords D) := by
  dsimp only
  obtain ⟨τ,xs,hr,hInd,hSpan,_,_,hOut⟩ := rawRankedForms_run D F T S j hd hn
  refine ⟨τ,xs,?_,hInd,hSpan,hOut⟩
  unfold rankedFormsRun
  rw [rankedFormsExtension_eq D F T S]
  exact hr.mono (rawRankedFormsCost_le D F T S j hd hn)

/-- A single binary polynomial-time machine emits the exact accessible
retained-full-rank forms in order, with one shared basis for the raw cut. -/
theorem rawRankedForms_binary (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) :
    ∃ g, TuringPolytime g ∧
      ∀ {d n : ℕ} (T S : Tensor K ((d+1)+(d+1)) n), 1 ≤ d → 2 ≤ n →
        ∃ xs : Fin (cutKernelDimension T S j) → Coord (d+1) n → K,
          LinearIndependent K xs ∧
          Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
          g (comparisonInput D T S)=(rankedBasisForms D xs).flatMap (cutFormWords D) := by
  obtain ⟨g,hg,he⟩ := EvenTI.P15Execution.totalBinary_of_boundedWordRuns
    (rawRankedValid D) (rankedFormsReference D F j) (rawRankedForms D F j)
      (cutWordPoly F) (rawRankedFormsPoly F j) (by
      intro _ ha
      obtain ⟨d,n,T,S,hd,hn,rfl⟩ := ha
      obtain ⟨τ,_,h,_,_,_⟩ := rankedFormsRun_ready D F T S j hd hn
      exact ⟨rankedFormsExtension F _,τ,h,(rankedFormsReference_eq h).symm⟩)
  refine ⟨g,hg,?_⟩
  intro d n T S hd hn
  obtain ⟨τ,xs,hRun,hInd,hSpan,hOut⟩ := rankedFormsRun_ready D F T S j hd hn
  exact ⟨xs,hInd,hSpan,(he _ ⟨d,n,T,S,hd,hn,rfl⟩).trans ((rankedFormsReference_eq hRun).trans hOut)⟩

#print axioms rawRankedFormsCost_le
#print axioms rawRankedForms_binary
end EvenTI.P18Trial
