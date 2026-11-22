import EvenP15TrialFieldVector
import EvenP10TrialWordAttempt
import EvenP15RequestHeader
import Mathproof.Meta.Problem18IMPNaturalPower20261001
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace EvenTI.P16Recover

open EvenTI.Action EvenTI.Contract EvenTI.P15Trial EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem rangeMap_eq_ofFn {A : Type} (f : ℕ → A) (r : ℕ) :
    (List.range r).map f = List.ofFn (fun i : Fin r => f i.val) := by
  apply List.ext_getElem (by simp)
  intros
  simp

private theorem singletonFlatMap {A B : Type} (f : A → B) (xs : List A) :
    xs.flatMap (fun x => [f x]) = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.flatMap_cons] using congrArg (List.cons (f x)) ih

/-- Row-major memory is precisely the order of the public transporter words. -/
theorem transporterOutput_of_contiguous {d n : ℕ} (D : FieldEncoding K) (g : Changes K d n)
    (count start : ℕ) (read : ℕ → K)
    (hCoordinates : ∀ (i : Fin d) (j k : Fin n), read (start + (i.val*(n*n)+(j.val*n+k.val))) = (g i).val j k) :
    [2,count] ++ (List.range (d*(n*n))).map (fun t => (D (read (start+t))).val) =
      transporterOutput D g count := by
  unfold transporterOutput
  apply congrArg (List.append [2,count])
  rw [rangeMap_eq_ofFn,List.ofFn_mul]
  simp only [List.ofFn_eq_map, ← List.flatMap_def]
  apply congrArg ((List.finRange d).flatMap)
  funext i
  rw [← List.ofFn_eq_map,List.ofFn_mul]
  simp only [List.ofFn_eq_map, ← List.flatMap_def]
  apply congrArg ((List.finRange n).flatMap)
  funext j
  unfold fieldWords
  rw [singletonFlatMap]
  apply congrArg (fun f : Fin n → ℕ => (List.finRange n).map f)
  funext k
  rw [hCoordinates i j k]

#print axioms transporterOutput_of_contiguous

def transporterCount : String := "even.recovery.output.count"

noncomputable def emitTransporter (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (.write (.lit 2)) (.seq (.write (.var transporterCount)) (fieldVectorProgram D F))

def emitTransporterCost (F : FieldPresentation K) (d n : ℕ) : ℕ :=
  (emitFieldLabelCost F+16)*(d*(n*n))+10

/-- Emit the complete witness packet from live contiguous matrix entries.
The tag, count, and field-coordinate encoding match the comparison contract. -/
theorem emitTransporter_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n a : ℕ} {s : Env} (g : Changes K d n)
    (hSlots : Slots F canonical qN.WS S B s)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hB : 2 < B)
    (hCount : (Fintype.card K-1)^(d-1) < B)
    (hCountReg : s.vars transporterCount=(Fintype.card K-1)^(d-1))
    (hFit : a+d*(n*n) ≤ S) (hA : s.vars fieldVectorStart=a)
    (hLength : s.vars fieldVectorLength=d*(n*n))
    (hData : ∀ (i : Fin d) (j k : Fin n),
      val F canonical qN.WS s (a+(i.val*(n*n)+(j.val*n+k.val))) = (g i).val j k) :
    ∃ t, Run B (emitTransporter D F) s t (emitTransporterCost F d n) ∧
      t.out = s.out ++ attemptOutput D (some g) ∧ t.arrs = s.arrs ∧ t.inp = s.inp := by
  let c := (Fintype.card K-1)^(d-1)
  let u := {s with out := s.out ++ [2]}
  let v := {u with out := u.out ++ [c]}
  have r₁ : Run B (.write (.lit 2)) s u 2 := Run.write (evalB_lit hB)
  have r₂ : Run B (.write (.var transporterCount)) u v 2 := Run.write
    (evalB_var_iff.mpr ⟨hCountReg.symm,hCountReg ▸ hCount⟩)
  obtain ⟨t,r₃,hT,hArr,hInp,_⟩ := fieldVectorProgram_run D F (σ:=v) (Mathproof.P15GEInit20261007.slots_frame F hSlots rfl rfl (fun _ _ => rfl) rfl) hQ hP
    (by omega) hFit hA hLength
  have rr : Run B (emitTransporter D F) s t (emitTransporterCost F d n) :=
    (r₁.seq (r₂.seq r₃)).mono (by unfold emitTransporterCost; omega)
  refine ⟨t,rr,?_,hArr,hInp⟩
  have hW := transporterOutput_of_contiguous D g c a (val F canonical qN.WS s) hData
  change t.out = s.out ++ transporterOutput D g c
  change t.out = ((s.out ++ [2]) ++ [c]) ++ (List.range (d*(n*n))).map
    (fun j => (D (val F canonical qN.WS s (a+j))).val) at hT
  rw [hT,← hW]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

#print axioms emitTransporter_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open EvenTI.Action EvenTI.Contract EvenTI.P15Trial EvenTI.P15Execution EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18IMPNaturalPower20261001 (Names naturalPowerRoutine naturalPower_run state)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def countNames : Names := ⟨"even.recovery.output.base", "even.recovery.output.order",
  transporterCount, "even.recovery.output.index"⟩

def initializeCount (q : ℕ) : Com :=
  .seq (.assign countNames.base (.lit (q-1)))
    (.assign countNames.exponent (.sub (.var requestOrder) (.lit 1)))

noncomputable def emitSuccessfulAttempt (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (initializeCount (Fintype.card K)) <|
    .seq (naturalPowerRoutine countNames) (emitTransporter D F)

def emitSuccessfulAttemptCost (F : FieldPresentation K) (d n : ℕ) : ℕ :=
  6 + (20*((d-1)+1)+emitTransporterCost F d n)

/-- Pay for the count and exact packet, from the original order and recovered matrix bank. -/
theorem emitSuccessfulAttempt_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n a : ℕ} {s : Env} (g : Changes K d n)
    (hSlots : Slots F canonical qN.WS S B s)
    (hQ : Fintype.card K ≤ B) (hP : F.p < B) (hB : 2 < B) (hD : d < B)
    (hCount : (Fintype.card K-1)^(d-1) < B) (hOrder : s.vars requestOrder=d)
    (hFit : a+d*(n*n) ≤ S) (hA : s.vars fieldVectorStart=a)
    (hLength : s.vars fieldVectorLength=d*(n*n))
    (hData : ∀ (i : Fin d) (j k : Fin n),
      val F canonical qN.WS s (a+(i.val*(n*n)+(j.val*n+k.val))) = (g i).val j k) :
    ∃ t, Run B (emitSuccessfulAttempt D F) s t (emitSuccessfulAttemptCost F d n) ∧
      t.out = s.out ++ attemptOutput D (some g) ∧ t.arrs = s.arrs ∧ t.inp = s.inp := by
  let q := Fintype.card K
  have hq : 1 < q := Fintype.one_lt_card
  let u := s.setVar countNames.base (q-1)
  let v := u.setVar countNames.exponent (d-1)
  have hQ' : q-1 < B := by change q ≤ B at hQ; omega
  have hRead : (Expr.var requestOrder).evalB B u = some d :=
    evalB_var_iff.mpr ⟨hOrder.symm,hOrder ▸ hD⟩
  have r₀ : Run B (.assign countNames.base (.lit (q-1))) s u 2 := Run.assign (evalB_lit hQ')
  have r₁ : Run B (.assign countNames.exponent (.sub (.var requestOrder) (.lit 1))) u v 4 :=
    Run.assign (evalB_bin (op := .sub) hRead (evalB_lit (by omega : 1 < B)) (by change d-1 < B; omega))
  have hBase : v.vars countNames.base = q-1 := by simp [u,v,countNames]
  have hExp : v.vars countNames.exponent = d-1 := by simp [v]
  let w := state countNames v (d-1)
  have r₂ : Run B (naturalPowerRoutine countNames) v w (20*((d-1)+1)) := by
    have hExpBound : v.vars countNames.exponent < B := by rw [hExp]; omega
    have hBaseBound : v.vars countNames.base < B := hBase.symm ▸ hQ'
    have hPow : ∀ i ≤ v.vars countNames.exponent, v.vars countNames.base^i < B := by
      rw [hExp,hBase]
      intro i hi
      exact (Nat.pow_le_pow_right (by omega : 0 < q-1) hi).trans_lt hCount
    simpa only [hExp] using naturalPower_run countNames v (by decide) (by decide) (by decide)
      hExpBound hBaseBound hPow
  have hsU : Slots F canonical qN.WS S B u := Slots.setVar F canonical hSlots (by decide) (by decide) _
  have hsV : Slots F canonical qN.WS S B v := Slots.setVar F canonical hsU (by decide) (by decide) _
  have hsW : Slots F canonical qN.WS S B w :=
    Slots.setVar F canonical (Slots.setVar F canonical hsV (by decide) (by decide) _) (by decide) (by decide) _
  have hC : w.vars transporterCount = (q-1)^(d-1) := by
    have ht : (state countNames v (d-1)).vars countNames.out = v.vars countNames.base^(d-1) := by
      simp [state,countNames,transporterCount,Env.setVar]
    exact ht.trans (congrArg (fun a => a^(d-1)) hBase)
  have hStart : w.vars fieldVectorStart = a := by
    simpa [w,state,v,u,countNames,transporterCount,fieldVectorStart] using hA
  have hSize : w.vars fieldVectorLength = d*(n*n) := by
    simpa [w,state,v,u,countNames,transporterCount,fieldVectorLength] using hLength
  have hVals (j : ℕ) : val F canonical qN.WS w j = val F canonical qN.WS s j := by
    dsimp only [w,state,v,u]
    rw [val_setVar F canonical (show countNames.index ≠ qN.WS by decide),
      val_setVar F canonical (show countNames.out ≠ qN.WS by decide),
      val_setVar F canonical (show countNames.exponent ≠ qN.WS by decide),
      val_setVar F canonical (show countNames.base ≠ qN.WS by decide)]
  obtain ⟨t,r₃,hOut,hArr,hInp⟩ := emitTransporter_run D F g hsW hQ hP hB hCount hC
    hFit hStart hSize (fun i j k => (hVals _).trans (hData i j k))
  exact ⟨t,(r₀.seq r₁).seq (r₂.seq r₃),hOut,hArr,hInp⟩

#print axioms emitSuccessfulAttempt_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def recoveryOutputReady : String := "even.recovery.output.ready"

noncomputable def emitRecoveryAttempt (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .ite (.eq (.var recoveryOutputReady) (.lit 0)) (.write (.lit 0)) (emitSuccessfulAttempt D F)

/-- A rejected attempt writes the single zero required by the comparison codec. -/
theorem emitRecoveryAttempt_none_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B d n : ℕ} {s : Env} (hB : 0 < B) (hTag : s.vars recoveryOutputReady=0) :
    Run B (emitRecoveryAttempt D F) s
      {s with out := s.out ++ attemptOutput D (none : Option (Changes K d n))} 6 := by
  have hLit : (Expr.lit 0).evalB B s = some 0 := evalB_lit hB
  have hVar : (Expr.var recoveryOutputReady).evalB B s = some 0 :=
    evalB_var_iff.mpr ⟨hTag.symm,hTag ▸ hB⟩
  exact Run.ite_true (evalB_condEq hVar hLit) (Run.write hLit)

/-- The constant-cost final status test permits the paid successful writer to run. -/
theorem emitRecoveryAttempt_some_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B k : ℕ} {s t : Env} (hB : 1 < B) (hTag : s.vars recoveryOutputReady=1)
    (hr : Run B (emitSuccessfulAttempt D F) s t k) :
    Run B (emitRecoveryAttempt D F) s t (4+k) := by
  have hLit : (Expr.lit 0).evalB B s = some 0 := evalB_lit (by omega)
  have hVar : (Expr.var recoveryOutputReady).evalB B s = some 1 :=
    evalB_var_iff.mpr ⟨hTag.symm,hTag ▸ hB⟩
  exact Run.ite_false (evalB_condEq hVar hLit) hr

#print axioms emitRecoveryAttempt_none_run
#print axioms emitRecoveryAttempt_some_run
end EvenTI.P16Recover

namespace EvenTI.P16Recover

open EvenTI.P15Trial
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)

/-- The scalar transporter count fits in at most q times the original order
plus one bits. No count-size assumption about the selected branch is needed. -/
theorem transporterCount_word_bound (q d : ℕ) :
    (q-1)^(d-1) < 2^(q*d+1) := by
  calc
    (q-1)^(d-1) ≤ (2^q)^(d-1) :=
      Nat.pow_le_pow_left ((Nat.sub_le q 1).trans (Nat.lt_two_pow_self (n:=q)).le) _
    _ ≤ (2^q)^d := Nat.pow_le_pow_right (by positivity) (Nat.sub_le d 1)
    _ = 2^(q*d) := (pow_mul 2 q d).symm
    _ < 2^(q*d+1) := Nat.pow_lt_pow_right (by decide) (by omega)

/-- A cubic original-header bound covers the count, all mode/row/column
words, and branch-independent field-label lookup. -/
theorem emitSuccessfulAttemptCost_le {K : Type} [Field K] [Fintype K] (F : FieldPresentation K)
    {d n L : ℕ} (hd : d ≤ L) (hn : n ≤ L) :
    emitSuccessfulAttemptCost F d n ≤ (emitFieldLabelCost F+52)*(L+1)^3 := by
  let X := L+1
  have hX : 0 < X := by dsimp [X]; omega
  have hdX : d ≤ X := hd.trans (Nat.le_succ _)
  have hnX : n ≤ X := hn.trans (Nat.le_succ _)
  have hArea : d*(n*n) ≤ X^3 := by
    calc d*(n*n) ≤ X*(X*X) := Nat.mul_le_mul hdX (Nat.mul_le_mul hnX hnX)
    _ = X^3 := by ring
  have hx3 : X ≤ X^3 := by simpa using (Nat.pow_le_pow_right hX (show 1≤3 by decide))
  have hpow : 1 ≤ X^3 := (by omega : 1 ≤ X).trans hx3
  have hd3 : (d-1)+1 ≤ X^3 := (by dsimp [X]; omega : (d-1)+1≤X).trans hx3
  have hm := Nat.mul_le_mul_left (emitFieldLabelCost F+16) hArea
  have he := Nat.mul_le_mul_left 20 hd3
  change emitSuccessfulAttemptCost F d n ≤ (emitFieldLabelCost F+52)*X^3
  unfold emitSuccessfulAttemptCost emitTransporterCost
  have hsum : (emitFieldLabelCost F+52)*X^3 =
      (emitFieldLabelCost F+16)*X^3+20*X^3+16*X^3 := by ring
  rw [hsum]
  omega

#print axioms transporterCount_word_bound
#print axioms emitSuccessfulAttemptCost_le
end EvenTI.P16Recover
