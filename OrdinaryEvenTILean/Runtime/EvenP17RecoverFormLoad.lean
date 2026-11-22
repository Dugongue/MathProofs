import EvenP17RecoverDigitWindow
import EvenP17RecoverWindows

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace EvenTI.P17Recover

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.P10Scan EvenTI.P12Compare
open EvenTI.P12CountPre
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def cutFormValues {a n : ℕ} (p : Coord a n → K) : List K :=
  List.ofFn (fun i : Fin (n^a) => p ((cutOrder a n).symm i))

def trialFormValues {l n : ℕ} : PreparedTrial K l n → List K
  | .reciprocal _ => []
  | .orderFour _ p _ _ => cutFormValues p.1 ++ cutFormValues p.2
  | .higher p _ => cutFormValues p.1 ++ cutFormValues p.2

theorem trialFormValues_encoded (D : FieldEncoding K) {l n : ℕ} (P : PreparedTrial K l n) :
    (trialFormValues P).map (fun x => (D x).val)=trialFormWords D P := by
  cases P <;> simp [trialFormValues,trialFormWords,cutFormValues,cutFormWords,List.map_ofFn,Function.comp_def]

noncomputable def loadTrialForms (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  loadFieldWindow D F (formStart right) (formEnd right) 0

/-- Decode both form vectors in the prepared records' exact coordinate order
and install them into consecutive slots. Reciprocal records have no form words. -/
theorem loadTrialForms_run (D : FieldEncoding K) (F : FieldPresentation K)
    {l n B S base : ℕ} {s : Env} (z a : List ℕ) (right : Bool) (P : PreparedTrial K l n)
    (hSec : OperandSections z right a (trialFormWords D P) s)
    (hS : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B) (hB : 1 < B)
    (hLen : z.length < B) (hBank : s.arrs "data"=sentinelWords z)
    (hBase : s.vars loadBase=base) (hFit : base+(trialFormValues P).length ≤ S) :
    ∃ t, Run B (loadTrialForms D F right) s t
      (11+encodedBankLoadCost F contiguousAddress (trialFormValues P).length) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ j (hj : j < (trialFormValues P).length),
        val F canonical qN.WS t (base+j)=(trialFormValues P)[j]) ∧
      (∀ j, j < base ∨ base+(trialFormValues P).length ≤ j →
        val F canonical qN.WS t j=val F canonical qN.WS s j) ∧
      t.arrs "data"=sentinelWords z ∧ t.inp=s.inp ∧ t.out=s.out := by
  have hWords := hSec.forms
  rw [← trialFormValues_encoded D P] at hWords
  obtain ⟨t,rt,ht,hValues,hOutside,_,hArr,hIn,hOut⟩ :=
    loadFieldWindow_run D F z (trialFormValues P) (formStart right) (formEnd right) 0
      hS hQ hB (by simpa using hSec.ordered.2.1) hSec.ordered.2.2 hLen rfl rfl
      (by cases right <;> decide) (by cases right <;> decide)
      (by cases right <;> decide) (by cases right <;> decide) hBase hFit
      (by simpa using hWords) hBank
  exact ⟨t,rt,ht,hValues,hOutside,(hArr _ (by decide)).trans hBank,hIn,hOut⟩

#print axioms loadTrialForms_run
end EvenTI.P17Recover
