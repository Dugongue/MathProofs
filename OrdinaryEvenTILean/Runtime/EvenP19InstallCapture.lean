import EvenP18TrialRawRankedForms
import EvenP17TrialTwoCapturedCuts

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace EvenTI.P19Install

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P12Compare EvenTI.P12ComparePrep
open EvenTI.P16Trial EvenTI.P17Trial EvenTI.P18Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax51.BinaryWordEncoding
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18P37Isolation20261004
open Mathproof.Problem18P37HostProgram20261004 (pre pre_ne_host)
open Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem rankedBasisForms_length_le (D : FieldEncoding K) {d n c : ℕ}
    (xs : Fin c → Coord (d+1) n → K) : (rankedBasisForms D xs).length ≤ n := by
  unfold rankedBasisForms linearChoices
  exact (List.length_filter_le _ _).trans (by
    rw [List.length_map]
    exact coefficientChoices_length_le D c n)

theorem formWords_length (D : FieldEncoding K) {d n : ℕ}
    (xs : List (Coord d n → K)) :
    (xs.flatMap (cutFormWords D)).length = xs.length*n^d := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,cutFormWords,List.length_ofFn] at *
    rw [ih,List.length_cons,Nat.succ_mul,Nat.add_comm]

noncomputable def captureRankedForms (D : FieldEncoding K) (F : FieldPresentation K)
    (j : Fin 4) (tag : String) : Com := iso (cutFormIso tag) (rawRankedForms D F j)

/-- Execute the rank-filtered raw producer in a capture namespace and
publish its literal form words on the host array. -/
theorem captureRankedForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {d n B : ℕ} (T U : Tensor K ((d+1)+(d+1)) n) (j : Fin 4) (tag : String)
    (hd : 1 ≤ d) (hn : 2 ≤ n) (s : Env) (prefixWords R : List ℕ) :
    let c := cutKernelDimension T U j
    let w := comparisonInput D T U
    let L := bitSize w
    let m := n^(d+1)
    let ext := comparisonInitExt F (pairCutSlotCount.value m) w.length (cutChoiceExt L)
    (cutWordPoly F).eval L ≤ B →
    (∀ r, s.vars (pre tag r)=0) →
    (∀ a, s.arrs (pre tag a)=List.replicate (ext a) 0) →
    s.vars formInputCursor=0 →
    (∃ suffixWords, s.arrs formInputTape=(w.length::w)++suffixWords) →
    (s.arrs formInputTape).length<B →
    (∀ v∈s.arrs formInputTape, v<B) →
    s.vars formOutputCursor=prefixWords.length →
    (s.arrs formOutputTape).take prefixWords.length=prefixWords →
    (s.arrs formOutputTape).length=R.length →
    R.length<B →
    (s.arrs formOutputTape).drop prefixWords.length=R.drop prefixWords.length →
    prefixWords.length+n*m≤R.length →
    ∃ (t : Env) (xs : Fin c → Coord (d+1) n → K),
      Run B (captureRankedForms D F j tag) s t (7*rawRankedFormsCost F (Fintype.card K) c d m n L j) ∧
      LinearIndependent K xs ∧
      Submodule.span K (Set.range xs)=selectedKernel (leftOf j) (if targetOf j then U else T) ∧
      t.vars formOutputCursor=prefixWords.length+(rankedBasisForms D xs).length*m ∧
      (t.arrs formOutputTape).take (t.vars formOutputCursor)=
        prefixWords++(rankedBasisForms D xs).flatMap (cutFormWords D) ∧
      (t.arrs formOutputTape).length=R.length ∧
      (t.arrs formOutputTape).drop (t.vars formOutputCursor)=R.drop (t.vars formOutputCursor) ∧
      t.arrs formInputTape=s.arrs formInputTape ∧ Frame (cutFormIso tag) s t := by
  dsimp only
  intro hB hv ha hPin hTape hTinLen hTinWord hPout hOut hLen hR hRest hCap
  obtain ⟨r,xs,hr,hInd,hSpan,_,_,hResult⟩ := rawRankedForms_run D F T U j hd hn
  have hLenOut := formWords_length D (rankedBasisForms D xs)
  have hRfit : prefixWords.length+r.out.length ≤ R.length := by
    rw [hResult,hLenOut]
    exact (Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (rankedBasisForms_length_le D xs)) _).trans hCap
  obtain ⟨t,rt,inv,fr⟩ := iso_run (cutFormIso_fresh tag) (cutRunWordLift hB hr) s prefixWords R
    hv ha hPin hTape hTinLen hTinWord (fun h => by cases h)
    (fun _ => hPout) (fun _ => hOut) (fun _ => hLen) (fun _ => hR) (fun _ => hRest)
    (fun _ => hRfit)
  refine ⟨t,xs,rt,hInd,hSpan,?_,?_,inv.outLen rfl,inv.outRest rfl,?_,fr⟩
  · have h := inv.outPtr rfl
    rw [hResult,hLenOut] at h
    exact h
  · exact (inv.outArr rfl).trans (congrArg (prefixWords ++ ·) hResult)
  · exact fr.arrs _ (fun y => (pre_ne_host tag y "even.form.raw").symm)
      (show formInputTape≠formOutputTape by decide)

#print axioms captureRankedForms_run
#print axioms rankedBasisForms_length_le
end EvenTI.P19Install
