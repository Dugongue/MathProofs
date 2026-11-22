import EvenP16TrialRawFormClock
import EvenP15Totalizer
import EvenP11WordsCount

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace EvenTI.P16Trial

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12ComparePrep EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax51.TuringPolytime Lax51.BinaryWordEncoding Polynomial
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def selectedFormRequest (raw : List ℕ) (code : ℕ) : List ℕ := raw.length::raw++[code]

private def unpackSelectedPair (x : List ℕ) : List ℕ := x.tail.take (x.headD 0)

private theorem unpackSelectedPair_request (raw : List ℕ) (code : ℕ) :
    unpackSelectedPair (selectedFormRequest raw code)=raw := by
  simp [unpackSelectedPair,selectedFormRequest]

private noncomputable def selectedFormExtension (F : FieldPresentation K) (x : List ℕ) :
    String → ℕ :=
  let w := unpackSelectedPair x
  let width := w[1]?.getD 0
  let order := (w.headD 0)/2
  comparisonInitExt F (pairCutSlotCount.value (width^order)) w.length (cutChoiceExt (bitSize w))

private theorem selectedFormExtension_request (D : FieldEncoding K) (F : FieldPresentation K)
    {d n : ℕ} (T S : Tensor K (d+d) n) (v : ℕ) :
    selectedFormExtension F (selectedFormRequest (comparisonInput D T S) v) =
      comparisonInitExt F (pairCutSlotCount.value (n^d)) (comparisonInput D T S).length
        (cutChoiceExt (bitSize (comparisonInput D T S))) := by
  unfold selectedFormExtension
  rw [unpackSelectedPair_request]
  simp [comparisonInput,show (d+d)/2=d by omega]

private theorem eval_nat_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact Nat.add_le_add hp hq
  | monomial i c =>
    simp only [eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

private def dummy : String := "even.trial.selected-form.outer-length"

private def discardOuterLength : Com := .seq (.read dummy) (.assign dummy (.lit 0))

private theorem discardOuterLength_run {B : ℕ} (ext : String → ℕ) (x : List ℕ) (hB : 0 < B) :
    Run B discardOuterLength (initEnv ext (x.length::x)) (initEnv ext x) 3 := by
  let σ := initEnv ext (x.length::x)
  let η := {σ.setVar dummy x.length with inp := x}
  have hr : Run B (.read dummy) σ η 1 := Run.read rfl
  have ha : Run B (.assign dummy (.lit 0)) η (η.setVar dummy 0) 2 :=
    Run.assign (evalB_lit hB)
  have he : η.setVar dummy 0=initEnv ext x := by
    have hv : (η.setVar dummy 0).vars=(initEnv ext x).vars := by
      funext r
      by_cases h : r=dummy <;> simp [η,σ,initEnv,Env.setVar,h]
    exact congrArg (fun vars => Env.mk vars (fun name => List.replicate (ext name) 0) x []) hv
  rw [he] at ha
  exact hr.seq ha

private noncomputable def selectedFormProgram (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) : Com := .seq discardOuterLength (rawSelectedForm D F j)

private noncomputable def selectedFormWordBudget (F : FieldPresentation K) : Polynomial ℕ :=
  C 1+cutWordPoly F

private noncomputable def selectedFormTimeBudget (F : FieldPresentation K) (j : Fin 4) : Polynomial ℕ :=
  C 3+rawSelectedFormPoly F j

private def isSelectedFormRequest (D : FieldEncoding K) (j : Fin 4) (x : List ℕ) : Prop :=
  ∃ (d n : ℕ) (T S : Tensor K (d+d) n) (v : Fin (Fintype.card K ^ cutKernelDimension T S j)),
    2≤d ∧ 2≤n ∧ Fintype.card K ^ cutKernelDimension T S j≤n ∧
      x=selectedFormRequest (comparisonInput D T S) v.val

private def SelectedFormRun (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4)
    (x : List ℕ) (τ : Env) : Prop :=
  Run ((selectedFormWordBudget F).eval (bitSize x)) (selectedFormProgram D F j)
    (initEnv (selectedFormExtension F x) (x.length::x)) τ ((selectedFormTimeBudget F j).eval (bitSize x))

private noncomputable def selectedFormReference (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (x : List ℕ) : List ℕ := by
  classical
  exact if h : ∃ τ, SelectedFormRun D F j x τ then (Classical.choose h).out else []
private theorem selectedRequest_run (D : FieldEncoding K) (F : FieldPresentation K) {d n : ℕ}
    (T S : Tensor K (d+d) n) (j : Fin 4) (hd : 2≤d) (hn : 2≤n)
    (v : Fin (Fintype.card K ^ cutKernelDimension T S j))
    (hv : Fintype.card K ^ cutKernelDimension T S j≤n) :
    let x := selectedFormRequest (comparisonInput D T S) v.val
    ∃ (τ : Env) (xs : Fin (cutKernelDimension T S j) → Coord d n → K),
      SelectedFormRun D F j x τ ∧ LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
      τ.out=cutFormWords D (fun y => ∑ i, coefficients D (cutKernelDimension T S j) v i * xs i y) := by
  dsimp only
  let w := comparisonInput D T S
  let x := selectedFormRequest w v.val
  let B := (selectedFormWordBudget F).eval (bitSize x)
  have hSize : bitSize w ≤ bitSize x := by
    change _ ≤ bitSize ((w.length::w)++[v.val])
    rw [EvenTI.P10Words.bitSize_append,Lax51Proofs.Encoding.bitSize_cons]
    omega
  have hb : (cutWordPoly F).eval (bitSize w) ≤ B := by
    have hh := eval_nat_mono (cutWordPoly F) hSize
    simp only [B,selectedFormWordBudget,eval_add,eval_C]
    omega
  have hB : 0 < B := by simp [B,selectedFormWordBudget]
  obtain ⟨τ,xs,hR,hInd,hSpan,hOut,_⟩ := rawSelectedForm_bit_run D F T S j hd hn v hv
  have hBody : Run B (rawSelectedForm D F j)
      (initEnv (selectedFormExtension F x) x) τ ((rawSelectedFormPoly F j).eval (bitSize w)) := by
    rw [selectedFormExtension_request D F T S v.val]
    exact cutRunWordLift hb hR
  have hClock : 3+(rawSelectedFormPoly F j).eval (bitSize w) ≤
      (selectedFormTimeBudget F j).eval (bitSize x) := by
    have hh := eval_nat_mono (rawSelectedFormPoly F j) hSize
    simp only [selectedFormTimeBudget,eval_add,eval_C]
    omega
  have hr : SelectedFormRun D F j x τ :=
    ((discardOuterLength_run (selectedFormExtension F x) x hB).seq hBody).mono hClock
  exact ⟨τ,xs,hr,hInd,hSpan,hOut⟩

private theorem selectedFormReference_eq {D : FieldEncoding K} {F : FieldPresentation K}
    {j : Fin 4} {x : List ℕ} {τ : Env} (h : SelectedFormRun D F j x τ) :
    selectedFormReference D F j x=τ.out := by
  classical
  have hE : ∃ t, SelectedFormRun D F j x t := ⟨τ,h⟩
  unfold selectedFormReference
  rw [dif_pos hE]
  obtain ⟨k,_,h₁⟩ := Run.bigStep (Classical.choose_spec hE)
  obtain ⟨l,_,h₂⟩ := Run.bigStep h
  exact congrArg Env.out (BigStep.unique h₁ h₂).1

/-- A single binary polynomial-time machine produces the selected cut
form from every correctly framed and cap-admitted raw request. -/
theorem rawSelectedForm_binary (D : FieldEncoding K) (F : FieldPresentation K) (j : Fin 4) :
    ∃ g, TuringPolytime g ∧
      ∀ {d n : ℕ} (T S : Tensor K (d+d) n), 2≤d → 2≤n →
        ∀ v : Fin (Fintype.card K ^ cutKernelDimension T S j),
          Fintype.card K ^ cutKernelDimension T S j≤n →
            ∃ xs : Fin (cutKernelDimension T S j) → Coord d n → K,
              LinearIndependent K xs ∧
              Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then S else T) ∧
              g (selectedFormRequest (comparisonInput D T S) v.val)=
                cutFormWords D (fun y => ∑ i, coefficients D (cutKernelDimension T S j) v i * xs i y) := by
  have hCompile := EvenTI.P15Execution.totalBinary_of_boundedWordRuns
    (isSelectedFormRequest D j) (selectedFormReference D F j) (selectedFormProgram D F j)
      (selectedFormWordBudget F) (selectedFormTimeBudget F j) (by
    intro x hx
    obtain ⟨d,n,T,S,v,hd,hn,hv,rfl⟩ := hx
    obtain ⟨τ,_,hr,_,_,_⟩ := selectedRequest_run D F T S j hd hn v hv
    exact ⟨selectedFormExtension F _,τ,hr,(selectedFormReference_eq hr).symm⟩)
  obtain ⟨g,hg,hAgree⟩ := hCompile
  refine ⟨g,hg,?_⟩
  intro d n T S hd hn v hv
  obtain ⟨τ,xs,hr,hInd,hSpan,hOut⟩ := selectedRequest_run D F T S j hd hn v hv
  have hV : isSelectedFormRequest D j (selectedFormRequest (comparisonInput D T S) v.val) :=
    ⟨d,n,T,S,v,hd,hn,hv,rfl⟩
  exact ⟨xs,hInd,hSpan,(hAgree _ hV).trans ((selectedFormReference_eq hr).trans hOut)⟩

#print axioms rawSelectedForm_binary
end EvenTI.P16Trial