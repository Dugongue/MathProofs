import EvenP12ComparePrepInit
import Mathproof.Meta.P15DecideIMPEGens20261007
import Mathproof.Meta.P15DecideIMPRowKer20261007

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace EvenTI.P12ComparePrep

open EvenTI.Contract
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18IMPFieldLayout20261001 (countedLoop_run arrayWrites scalarWrites run_frame)
open Mathproof.Problem18IMPFieldAddition20261001 (writeValues writeValues_length writeValues_inside)
open Mathproof.P15DecideIMPEGens20261007 (ev_add ev_div ev_mul hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)

def coeffIndex : String := "even_compare_coefficient_index"
def coeffPower : String := "even_compare_coefficient_power"
def coeffNumber : String := "even_compare_coefficient_number"
def coeffLength : String := "even_compare_coefficient_length"
def coefficientBank : String := "even_compare_coefficient_digits"

def coefficientLabel (q v i : ℕ) : ℕ := v / q^i % q

def coefficientRemainder (q : ℕ) : Expr :=
  .bin .sub (.var coeffNumber) (.bin .mul (.bin .div (.var coeffNumber) (.lit q)) (.lit q))

def coefficientDigitBody (q : ℕ) (code : String) : Com :=
  .seq (.assign coeffNumber (.bin .div (.var code) (.var coeffPower)))
    (.seq (.store coefficientBank (.var coeffIndex) (coefficientRemainder q))
      (.seq (.assign coeffPower (.bin .mul (.var coeffPower) (.lit q)))
        (.assign coeffIndex (.add (.var coeffIndex) (.lit 1)))))

def coefficientDigitProgram (q : ℕ) (code : String) : Com :=
  .seq (.assign coeffIndex (.lit 0)) (.seq (.assign coeffPower (.lit 1))
    (.while (.lt (.var coeffIndex) (.var coeffLength)) (coefficientDigitBody q code)))

def coefficientDigitState (σ : Env) (q v i : ℕ) : Env :=
  let step := (σ.setVar coeffIndex i).setVar coeffPower (q^i)
  let step := if 0 < i then step.setVar coeffNumber (v / q^(i-1)) else step
  {step with arrs := fun a => if a=coefficientBank
      then writeValues (σ.arrs a) 0 (coefficientLabel q v) i else σ.arrs a}

/-- Decode a live bounded coefficient index as base-field-size digits, with
the same ascending coordinate order as the mathematical enumeration. -/
theorem coefficientDigitProgram_run (q v c B : ℕ) (code : String) (σ : Env)
    (hq : 0 < q) (hqB : q < B) (hB : 1 < B) (hv : v < B) (hc : c < B)
    (hPow : q^c < B) (hFit : c ≤ (σ.arrs coefficientBank).length)
    (hcLive : σ.vars coeffLength = c) (hvLive : σ.vars code = v)
    (hFresh : code ≠ coeffIndex ∧ code ≠ coeffPower ∧ code ≠ coeffNumber) :
    let τ := coefficientDigitState σ q v c
    Run B (coefficientDigitProgram q code) σ τ (34*c+8) ∧
      (∀ i < c, (τ.arrs coefficientBank).getD i 0 = coefficientLabel q v i) ∧
      τ.inp = σ.inp ∧ τ.out = σ.out := by
  let state := coefficientDigitState σ q v
  have hIndex (i : ℕ) : (state i).vars coeffIndex = i := by
    by_cases h : 0 < i <;> simp [state,coefficientDigitState,h,coeffIndex,coeffPower,coeffNumber]
  have hLength (i : ℕ) : (state i).vars coeffLength = c := by
    by_cases h : 0 < i <;>
      simp [state,coefficientDigitState,h,coeffIndex,coeffPower,coeffNumber,coeffLength] <;>
      exact hcLive
  have hCode (i : ℕ) : (state i).vars code = v := by
    by_cases h : 0 < i <;> simp [state,coefficientDigitState,h,hFresh.1,hFresh.2.1,hFresh.2.2,hvLive]
  have hPower (i : ℕ) : (state i).vars coeffPower = q^i := by
    by_cases h : 0 < i <;> simp [state,coefficientDigitState,h,coeffPower,coeffNumber]
  have hLen (i : ℕ) : ((state i).arrs coefficientBank).length = (σ.arrs coefficientBank).length := by
    simp [state,coefficientDigitState,writeValues_length]
  have hStep (i : ℕ) (hi : i<c) : Run B (coefficientDigitBody q code) (state i) (state (i+1)) 30 := by
    let s := state i
    let s₁ := s.setVar coeffNumber (v/q^i)
    let s₂ := s₁.setArr coefficientBank i (coefficientLabel q v i)
    let s₃ := s₂.setVar coeffPower (q^(i+1))
    have hiB : i < B := hi.trans hc
    have hNextB : i+1 < B := (Nat.succ_le_of_lt hi).trans_lt hc
    have hQi : q^i < B := (Nat.pow_le_pow_right hq hi.le).trans_lt hPow
    have hQn : q^(i+1) < B := (Nat.pow_le_pow_right hq hi).trans_lt hPow
    have hVB : v/q^i < B := (Nat.div_le_self ..).trans_lt hv
    have hRead (e : String) (a : ℕ) (he : s.vars e = a) (ha : a < B) :
        (Expr.var e).evalB B s = some a := (evalB_var_iff.mpr ⟨he.symm,he ▸ ha⟩)
    have r₁ : Run B (.assign coeffNumber (.bin .div (.var code) (.var coeffPower))) s s₁ 4 :=
      Run.assign (ev_div (hRead _ _ (hCode i) hv) (hRead _ _ (hPower i) hQi) hVB)
    have hIx : s₁.vars coeffIndex = i := by
      simpa only [s₁,s,vars_setVar,show coeffIndex ≠ coeffNumber by decide,if_false] using hIndex i
    have hV : (Expr.var coeffNumber).evalB B s₁ = some (v/q^i) := by
      rw [evalB_var_iff]; simp [s₁,hVB]
    have hDivB : v/q^i/q < B := (Nat.div_le_self ..).trans_lt hVB
    have hMulB : v/q^i/q*q < B := (Nat.div_mul_le_self ..).trans_lt hVB
    have hRemB : v/q^i-(v/q^i/q*q) < B := (Nat.sub_le ..).trans_lt hVB
    have hNum := ev_sub hV (ev_mul (ev_div hV (evalB_lit hqB) hDivB) (evalB_lit hqB) hMulB) hRemB
    rw [hmdg] at hNum
    have eRem : (coefficientRemainder q).evalB B s₁ = some (coefficientLabel q v i) := hNum
    have r₂ : Run B (.store coefficientBank (.var coeffIndex) (coefficientRemainder q)) s₁ s₂
        (1 + (Expr.var coeffIndex).size + (coefficientRemainder q).size) := by
      apply Run.store (evalB_var_iff.mpr ⟨hIx.symm,hIx ▸ hiB⟩) eRem
      have : (s₁.arrs coefficientBank).length = (σ.arrs coefficientBank).length := hLen i
      omega
    have eP : (Expr.var coeffPower).evalB B s₂ = some (q^i) := by
      have hh : s₂.vars coeffPower = q^i := by
        simpa only [s₂,s₁,s,vars_setArr,vars_setVar,show coeffPower ≠ coeffNumber by decide,if_false] using hPower i
      exact evalB_var_iff.mpr ⟨hh.symm,hh ▸ hQi⟩
    have r₃ : Run B (.assign coeffPower (.bin .mul (.var coeffPower) (.lit q))) s₂ s₃ 4 :=
      Run.assign (by rw [pow_succ] at hQn ⊢; exact ev_mul eP (evalB_lit hqB) hQn)
    have eI : (Expr.var coeffIndex).evalB B s₃ = some i := by
      have hh : s₃.vars coeffIndex = i := by
        simpa [s₃,s₂,show coeffIndex ≠ coeffPower by decide] using hIx
      exact evalB_var_iff.mpr ⟨hh.symm,hh ▸ hiB⟩
    have r₄ : Run B (.assign coeffIndex (.add (.var coeffIndex) (.lit 1))) s₃
        (s₃.setVar coeffIndex (i+1)) 4 :=
      Run.assign (ev_add eI (evalB_lit hB) hNextB)
    have eFinal : s₃.setVar coeffIndex (i+1) = state (i+1) := by
      cases σ
      by_cases hi0 : 0 < i <;>
        simp only [s₃,s₂,s₁,s,state,coefficientDigitState,Env.setVar,Env.setArr,writeValues,
          hi0, if_true, if_false, show 0 < i + 1 from Nat.zero_lt_succ i, Nat.add_sub_cancel]
      all_goals congr 1
      all_goals first
        | (funext x
           by_cases hI : x=coeffIndex
           · subst x; simp [coeffIndex,coeffPower,coeffNumber]
           · by_cases hP : x=coeffPower
             · subst x; simp [coeffIndex,coeffPower,coeffNumber]
             · by_cases hN : x=coeffNumber
               · subst x; simp [coeffIndex,coeffPower,coeffNumber]
               · simp [hI,hP,hN])
        | (funext a; by_cases ha : a=coefficientBank <;> simp [ha])
    rw [eFinal] at r₄
    exact (r₁.seq (r₂.seq (r₃.seq r₄))).mono (by simp [coefficientRemainder,Expr.size])
  let start := σ.setVar coeffIndex 0
  have rI : Run B (.assign coeffIndex (.lit 0)) σ start 2 := Run.assign (evalB_lit (by omega))
  have hStart : start.setVar coeffPower 1 = state 0 := by
    cases σ
    simp only [start,state,coefficientDigitState,Nat.not_lt_zero,if_false,pow_zero,Env.setVar,writeValues]
    congr 1
    funext a
    simp
  have rP : Run B (.assign coeffPower (.lit 1)) start (state 0) 2 := by
    rw [← hStart]
    exact Run.assign (evalB_lit hB)
  have hLoop := countedLoop_run coeffIndex coeffLength (coefficientDigitBody q code) state
    (fun i _ => hIndex i) (fun i _ => hLength i) hc hStep
  refine ⟨(rI.seq (rP.seq hLoop)).mono (by omega),?_,?_,?_⟩
  · intro i hi
    rw [show ((state c).arrs coefficientBank) =
      writeValues (σ.arrs coefficientBank) 0 (coefficientLabel q v) c by simp [state,coefficientDigitState]]
    simpa only [Nat.zero_add] using writeValues_inside (σ.arrs coefficientBank) 0 c i
      (coefficientLabel q v) (by omega) hi
  · by_cases h : 0 < c <;> simp [state,coefficientDigitState,h]
  · by_cases h : 0 < c <;> simp [state,coefficientDigitState,h]

variable {K : Type} [Field K] [Fintype K]

theorem coefficientLabel_eq (D : FieldEncoding K) {c : ℕ}
    (v : Fin (Fintype.card K ^ c)) (i : Fin c) :
    coefficientLabel (Fintype.card K) v.val i.val = (D (coefficients D c v i)).val := by
  simp [coefficientLabel,coefficients]

#print axioms coefficientDigitProgram_run
#print axioms coefficientLabel_eq
end EvenTI.P12ComparePrep
