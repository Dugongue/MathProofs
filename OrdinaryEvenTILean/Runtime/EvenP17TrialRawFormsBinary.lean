import EvenP17TrialRawForms
import EvenP15Totalizer

set_option autoImplicit false
set_option maxHeartbeats 1750000

namespace EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P15Trial EvenTI.P16Trial EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax51.TuringPolytime
open Lax51.BinaryWordEncoding (bitSize)
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

noncomputable def rawCutFormsPoly (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  rawNonzeroBitPoly F j+C emitFormInitCost+
    ((C 24*X+C (26+emitFieldLabelCost F))*X+C 6)*X

theorem rawCutFormsCost_le (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K (d+d) n) (j : Fin 4) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    let L := bitSize (comparisonInput D T S)
    rawCutFormsCost F (Fintype.card K) (cutKernelDimension T S j) d (n^d) n L j ≤
      (rawCutFormsPoly F j).eval L := by
  dsimp only
  let c := cutKernelDimension T S j
  let m := n^d
  let q := Fintype.card K
  let L := bitSize (comparisonInput D T S)
  let N := cappedCutChoiceCount q c n
  let E := (24*L+(26+emitFieldLabelCost F))*L+6
  obtain ⟨hnM,hmL,hdL⟩ := cutInput_side_bounds D T S (by omega : 1 ≤ d) hn
  have hnL := hnM.trans hmL
  have hcL : c ≤ L := (kernelFinrank_le _).trans hmL
  have hScan : 30*(m+q)+42+((visitCutCandidateCost F c m+8)*N+6) ≤
      (cutNonzeroPaidPoly F q).eval L :=
    nonzeroCutScanCost_le F hcL hmL hnL
  have hEmit : emitHigherFormCost F d m ≤ E := by
    simp only [emitHigherFormCost,E,Nat.add_assoc]
    gcongr
  have hCandidate : cutCandidateCost F c m ≤ visitCutCandidateCost F c m := by
    unfold visitCutCandidateCost
    omega
  have hOnce : encodeOneFormCost F c d m+8 ≤ (visitCutCandidateCost F c m+8)+E := by
    unfold encodeOneFormCost
    omega
  have hLoop := Nat.mul_le_mul_right N hOnce
  rw [Nat.add_mul (visitCutCandidateCost F c m+8) E N] at hLoop
  have hCount : N ≤ L := (cappedCutChoiceCount_le q c n).trans hnL
  have hTotal := Nat.mul_le_mul_left E hCount
  change rawCutFormsCost F q c d m n L j ≤ (rawCutFormsPoly F j).eval L
  simp only [rawCutFormsCost,rawCutFormsPoly,rawNonzeroBitPoly,eval_add,eval_C,
    eval_mul,eval_X,rawSetupBitPoly_eval]
  change rawCutSetupBitCost F L j+(emitFormInitCost+
    (30*(m+q)+42+((encodeOneFormCost F c d m+8)*N+6))) ≤
    rawCutSetupBitCost F L j+(cutNonzeroPaidPoly F q).eval L+emitFormInitCost+E*L
  omega

private def rawFormsValid (D : FieldEncoding K) (w : List ℕ) : Prop :=
  ∃ (d n : ℕ) (T S : Tensor K (d+d) n), 2 ≤ d ∧ 2 ≤ n ∧ w=comparisonInput D T S

private noncomputable def cutFormsExtension (F : FieldPresentation K) (w : List ℕ) : String → ℕ :=
  let d := (w.headD 0)/2
  let n := w[1]?.getD 0
  comparisonInitExt F (pairCutSlotCount.value (n^d)) w.length (cutChoiceExt (bitSize w))

private theorem cutFormsExtension_eq (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K (d+d) n) :
    cutFormsExtension F (comparisonInput D T S) =
      comparisonInitExt F (pairCutSlotCount.value (n^d)) (comparisonInput D T S).length
        (cutChoiceExt (bitSize (comparisonInput D T S))) := by
  simp [cutFormsExtension,comparisonInput,show (d+d)/2=d by omega]

private def cutFormsRun (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (w : List ℕ) (τ : Env) : Prop :=
  Run ((cutWordPoly F).eval (bitSize w)) (rawCutForms D F j)
    (initEnv (cutFormsExtension F w) (w.length::w)) τ ((rawCutFormsPoly F j).eval (bitSize w))

private noncomputable def cutFormsReference (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (w : List ℕ) : List ℕ := by
  classical
  exact if h : ∃ τ, cutFormsRun D F j w τ then h.choose.out else []

private theorem cutFormsReference_eq {D : FieldEncoding K} {F : FieldPresentation K}
    {j : Fin 4} {w : List ℕ} {τ : Env} (h : cutFormsRun D F j w τ) :
    cutFormsReference D F j w=τ.out := by
  classical
  have hE : ∃ t, cutFormsRun D F j w t := ⟨τ,h⟩
  unfold cutFormsReference
  rw [dif_pos hE]
  obtain ⟨k,_,h₁⟩ := Run.bigStep (Classical.choose_spec hE)
  obtain ⟨l,_,h₂⟩ := Run.bigStep h
  exact congrArg Env.out (BigStep.unique h₁ h₂).1

private theorem cutFormsRun_ready (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K (d+d) n) (j : Fin 4) (hd : 2 ≤ d) (hn : 2 ≤ n) :
    let c := cutKernelDimension T S j
    ∃ (τ : Env) (xs : Fin c → Coord d n → K), cutFormsRun D F j (comparisonInput D T S) τ ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=(List.range (cappedCutChoiceCount (Fintype.card K) c n)).flatMap (basisFormWords D xs) := by
  dsimp only
  obtain ⟨τ,xs,hr,hInd,hSpan,_,_,hOut⟩ := rawCutForms_run D F T S j hd hn
  refine ⟨τ,xs,?_,hInd,hSpan,hOut⟩
  unfold cutFormsRun
  rw [cutFormsExtension_eq D F T S]
  exact hr.mono (rawCutFormsCost_le D F T S j hd hn)

/-- Exact binary polynomial time from the literal raw pair through the
entire capped coefficient enumeration and all corresponding field-word
encodings, with a single shared basis for the list. -/
theorem rawCutForms_binary (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) :
    ∃ g, TuringPolytime g ∧
      ∀ {d n : ℕ} (T S : Tensor K (d+d) n), 2 ≤ d → 2 ≤ n →
        ∃ xs : Fin (cutKernelDimension T S j) → Coord d n → K,
          LinearIndependent K xs ∧
          Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
          g (comparisonInput D T S)=
            (List.range (cappedCutChoiceCount (Fintype.card K) (cutKernelDimension T S j) n)).flatMap
              (basisFormWords D xs) := by
  obtain ⟨g,hg,he⟩ := EvenTI.P15Execution.totalBinary_of_boundedWordRuns
    (rawFormsValid D) (cutFormsReference D F j) (rawCutForms D F j)
      (cutWordPoly F) (rawCutFormsPoly F j) (by
      intro _ ha
      obtain ⟨d,n,T,S,hd,hn,rfl⟩ := ha
      obtain ⟨τ,_,h,_,_,_⟩ := cutFormsRun_ready D F T S j hd hn
      exact ⟨cutFormsExtension F _,τ,h,(cutFormsReference_eq h).symm⟩)
  refine ⟨g,hg,?_⟩
  intro d n T S hd hn
  obtain ⟨τ,xs,hRun,hInd,hSpan,hOut⟩ := cutFormsRun_ready D F T S j hd hn
  exact ⟨xs,hInd,hSpan,(he _ ⟨d,n,T,S,hd,hn,rfl⟩).trans ((cutFormsReference_eq hRun).trans hOut)⟩

#print axioms rawCutFormsCost_le
#print axioms rawCutForms_binary
end EvenTI.P17Trial
